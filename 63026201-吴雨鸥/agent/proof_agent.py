#!/usr/bin/env python3
"""LeanTheoremAgent —— 形式化证明 Agent 的运行时骨架（harness）。

职责边界很清楚：
  * 本脚本 = 感知 + 验证 + 反思编排 + 记忆（快照/报告）
  * 修复（repair）由外部注入：可以是 LLM，也可以是人。
    用 --repair-cmd 指定一个命令，它接收 {file} 与 {diag} 两个占位符，
    负责就地修改 Lean 文件。

唯一的成功判据：`lake build <target>` 零 error。

用法示例
--------
  # 只验证一次，输出结构化诊断
  python proof_agent.py --project ../_toolchain/mathlib4 --file ../euclid/Euclid.lean --target Euclid

  # 带修复器的完整闭环（最多 8 轮）
  python proof_agent.py --project ... --file ... --target ... \
      --repair-cmd "python llm_repair.py --file {file} --diag {diag}"

  # 只做定理名探活
  python proof_agent.py --project ... --probe Nat.factorial_pos Nat.minFac_prime Nat.Prime.not_dvd_one
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from functools import cached_property
from dataclasses import dataclass, field, asdict

# Lean 诊断行： path:line:col: error(lean.unknownIdentifier): message
DIAG_RE = re.compile(r"^(?P<path>.+?):(?P<line>\d+):(?P<col>\d+):\s*(?P<sev>\w+)\((?P<code>[\w.]+)\):\s*(?P<msg>.*)$")

# 报错 → 分类 → 修复策略（对应 DESIGN.md 的策略表）
RULES: list[tuple[str, str, str]] = [
    (r"unknown (constant|identifier)", "unknown-constant",
     "定理名不存在：用 grep_theorem 在 mathlib 源码里搜真名，或换一条定理 / 自己证引理。"),
    (r"application type mismatch|has type.*but is expected to have type", "type-mismatch",
     "参数顺序或隐式参数错了：先 #check 打印签名再对齐。"),
    (r"type mismatch", "type-mismatch",
     "类型不一致：试 simpa [...] using / norm_num / exact_mod_cast。"),
    (r"unsolved goals", "unsolved-goal",
     "洞没填上：补 have 中间断言，或换 omega / linarith / nlinarith / ring_nf。"),
    (r"tactic '(omega|linarith|nlinarith|ring)' failed", "tactic-failed",
     "算术前提不足：先把缺失的不等式证出来，再调该 tactic。"),
    (r"failed to synthesize|OfNat", "typeclass", "类型推导歧义：补显式类型标注。"),
    (r"declaration uses 'sorry'|unsolved goals.*sorry", "sorry", "禁止 sorry，判失败。"),
    (r"heartbeats|maximum recursion|timeout", "resource", "项太大：拆成子引理 / 加 simp 中间步。"),
    (r"failed to fetch|unable to access|CONNECT tunnel", "network", "依赖拉取失败：重试或换网络通道。"),
]

SORRY_RE = re.compile(r"\b(sorry|admit)\b")


@dataclass
class Diagnostic:
    path: str
    line: int
    col: int
    severity: str
    code: str
    message: str
    category: str = "other"
    strategy: str = ""


@dataclass
class Attempt:
    n: int
    snapshot: str
    ok: bool
    elapsed: float
    diagnostics: list[Diagnostic] = field(default_factory=list)
    raw_tail: str = ""


def classify(msg: str) -> tuple[str, str]:
    for pat, cat, strat in RULES:
        if re.search(pat, msg, re.IGNORECASE):
            return cat, strat
    return "other", "人工阅读 diagnostics，定位到具体 goal 后局部改写。"


def parse_diagnostics(text: str) -> list[Diagnostic]:
    out: list[Diagnostic] = []
    for ln in text.splitlines():
        m = DIAG_RE.match(ln.rstrip())
        if not m:
            continue
        cat, strat = classify(m.group("msg"))
        out.append(Diagnostic(
            path=m.group("path"), line=int(m.group("line")), col=int(m.group("col")),
            severity=m.group("sev"), code=m.group("code"),
            message=m.group("msg"), category=cat, strategy=strat))
    return out


class Harness:
    def __init__(self, project: str, file: str, target: str,
                 lean_bin: str | None = None, attempts_dir: str = ".attempts",
                 git_proxy: str | None = None):
        self.project = os.path.abspath(project)
        self.file = os.path.abspath(file)
        self.target = target
        self.lean_bin = lean_bin
        self.attempts_dir = os.path.abspath(attempts_dir)
        self.git_proxy = git_proxy
        os.makedirs(self.attempts_dir, exist_ok=True)

    # ---------- 可执行文件（Windows 需要 .exe）----------
    @cached_property
    def lake_exe(self) -> str:
        base = "lake.exe" if os.name == "nt" else "lake"
        if self.lean_bin:
            return os.path.join(self.lean_bin, base)
        return base

    @cached_property
    def lean_exe(self) -> str:
        base = "lean.exe" if os.name == "nt" else "lean"
        if self.lean_bin:
            return os.path.join(self.lean_bin, base)
        return base

    # ---------- 环境 ----------
    def _env(self) -> dict:
        env = os.environ.copy()
        if self.lean_bin:
            env["PATH"] = self.lean_bin + os.pathsep + env.get("PATH", "")
        if self.git_proxy:
            env["GIT_CONFIG_COUNT"] = "2"
            env["GIT_CONFIG_KEY_0"] = "http.proxy"
            env["GIT_CONFIG_VALUE_0"] = self.git_proxy
            env["GIT_CONFIG_KEY_1"] = "https.proxy"
            env["GIT_CONFIG_VALUE_1"] = self.git_proxy
        return env

    # ---------- 工具 1：编译验证 ----------
    def lake_build(self) -> tuple[bool, str, list[Diagnostic]]:
        # 把待验证文件放进工程根目录，让 lake 能把它当模块编
        dst = os.path.join(self.project, os.path.basename(self.file))
        if os.path.abspath(dst) != self.file:
            shutil.copyfile(self.file, dst)
        t0 = time.time()
        proc = subprocess.run([self.lake_exe, "build", self.target],
                              cwd=self.project, env=self._env(),
                              capture_output=True, text=True, encoding="utf-8", errors="replace")
        elapsed = time.time() - t0
        text = (proc.stdout or "") + "\n" + (proc.stderr or "")
        diags = parse_diagnostics(text)
        errors = [d for d in diags if d.severity == "error"]
        ok = (proc.returncode == 0) and not errors
        return ok, text, errors

    # ---------- 工具 2：定理名探活 ----------
    def probe(self, names: list[str]) -> str:
        src = "\n".join(f"#check {n}" for n in names) + "\n"
        tmp = os.path.join(self.project, "_probe_tmp.lean")
        open(tmp, "w", encoding="utf-8").write(src)
        proc = subprocess.run([self.lean_exe, tmp], cwd=self.project, env=self._env(),
                              capture_output=True, text=True, encoding="utf-8", errors="replace")
        try:
            os.remove(tmp)
        except OSError:
            pass
        return (proc.stdout or "") + (proc.stderr or "")

    # ---------- 工具 3：源码检索 ----------
    @staticmethod
    def grep_theorem(pattern: str, root: str):
        try:
            proc = subprocess.run(["rg", "-n", "--no-heading", pattern, root],
                                  capture_output=True, text=True, encoding="utf-8", errors="replace")
            return proc.stdout
        except FileNotFoundError:
            return "(ripgrep 未安装，请改用系统搜索)"

    # ---------- 反思循环 ----------
    def run(self, max_attempts: int = 8, repair_cmd: str | None = None) -> int:
        history: list[Attempt] = []
        streak: dict[str, int] = {}

        for n in range(1, max_attempts + 1):
            snap = os.path.join(self.attempts_dir, f"{n:02d}_{os.path.basename(self.file)}")
            shutil.copyfile(self.file, snap)

            src = open(self.file, encoding="utf-8").read()
            sorry_hit = SORRY_RE.search(src)
            t0 = time.time()
            ok, text, errors = (False, "sorry detected", []) if sorry_hit else self.lake_build()
            att = Attempt(n=n, snapshot=snap, ok=ok, elapsed=time.time() - t0,
                          diagnostics=errors, raw_tail=text[-1500:])
            if sorry_hit:
                att.diagnostics.append(Diagnostic(self.file, 0, 0, "error", "lint.sorry",
                                                  "declaration uses 'sorry'", "sorry", "去掉 sorry"))
            history.append(att)
            print(f"--- attempt {n}: {'PASS' if ok else 'FAIL'} ({att.elapsed:.1f}s) ---", flush=True)
            for d in att.diagnostics[:12]:
                print(f"  [{d.category}] {os.path.basename(d.path)}:{d.line}:{d.col} {d.message[:120]}", flush=True)
                print(f"      -> {d.strategy}", flush=True)

            if ok:
                self._report(history, success=True)
                print(f"\nVERIFIED in {n} attempt(s). Proof: {self.file}", flush=True)
                return 0

            # 同类错误连出 3 次 => 升级策略
            cats = {d.category for d in att.diagnostics}
            for c in cats:
                streak[c] = streak.get(c, 0) + 1
            if any(v >= 3 for v in streak.values()):
                print("  !! 同类错误连续 3 次：建议 escalate（换定理 / 换构造 / 拆引理）", flush=True)

            if not repair_cmd:
                print("\n未提供 --repair-cmd，停止。卡点报告见 report.json", flush=True)
                self._report(history, success=False)
                return 1

            diag_json = os.path.join(self.attempts_dir, f"{n:02d}_diagnostics.json")
            open(diag_json, "w", encoding="utf-8").write(
                json.dumps([asdict(d) for d in att.diagnostics], ensure_ascii=False, indent=2))
            cmd = repair_cmd.format(file=self.file, diag=diag_json)
            subprocess.run(cmd, shell=True)

        self._report(history, success=False)
        print(f"\nSTUCK after {max_attempts} attempts. 见 report.json", flush=True)
        return 1

    def _report(self, history: list[Attempt], success: bool):
        data = {
            "theorem": self.target,
            "file": self.file,
            "success": success,
            "attempts": [
                {**{k: v for k, v in asdict(a).items() if k != "diagnostics"},
                 "diagnostics": [asdict(d) for d in a.diagnostics]}
                for a in history
            ],
        }
        out = os.path.join(self.attempts_dir, "report.json")
        open(out, "w", encoding="utf-8").write(json.dumps(data, ensure_ascii=False, indent=2))
        print(f"\nreport -> {out}", flush=True)


def main() -> int:
    ap = argparse.ArgumentParser(description="LeanTheoremAgent harness")
    ap.add_argument("--project", required=True, help="lake 工程根目录")
    ap.add_argument("--file", help="待验证的 .lean 文件")
    ap.add_argument("--target", help="lake build 目标（模块名）")
    ap.add_argument("--max-attempts", type=int, default=8)
    ap.add_argument("--repair-cmd", help='修复命令，可用 {file} {diag} 占位符')
    ap.add_argument("--lean-bin", help="lean/lake 可执行文件所在目录")
    ap.add_argument("--git-proxy", help="给 git 用的代理，如 http://127.0.0.1:53518")
    ap.add_argument("--attempts-dir", default=".attempts")
    ap.add_argument("--probe", nargs="*", help="只做 #check 探活：--probe Nat.foo Nat.bar")
    ap.add_argument("--grep", help="在 --grep-root 里搜定理")
    ap.add_argument("--grep-root", default=".")
    args = ap.parse_args()

    h = Harness(args.project, args.file or "", args.target or "",
                lean_bin=args.lean_bin, attempts_dir=args.attempts_dir, git_proxy=args.git_proxy)

    if args.probe:
        print(h.probe(args.probe))
        return 0
    if args.grep:
        print(Harness.grep_theorem(args.grep, args.grep_root))
        return 0
    if not (args.file and args.target):
        ap.error("需要 --file 与 --target")
    return h.run(max_attempts=args.max_attempts, repair_cmd=args.repair_cmd)


if __name__ == "__main__":
    sys.exit(main())
