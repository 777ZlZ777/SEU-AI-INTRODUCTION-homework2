# 第二次作业

- 姓名：匡天胤
- 学号：63Q26106
- 日期：2026-10-23

## 文件清单

| 文件 | 说明 |
|---|---|
| `report.pdf` | A4 一页报告（本次作业正文） |
| `report.md` | 同上内容的 Markdown 版，便于在 GitHub 上直接阅读 |
| `lean-auto.zip` | 实验源码（Python，纯标准库）：LLM 生成 → 静态闸门 → Lean 验证 → 公理审计 → 报错回灌 |
| `lean_auto-0.2.0-py3-none-any.whl` | 可安装的 Python 包（`pip install` 后得到 `lean-auto` 命令） |

## 实验概要

用大模型生成 Lean 4 证明，交给 Lean 4.36 + Mathlib 编译验证，失败则把完整代码与报错回灌重试。
两道命题均通过：

| 命题 | 轮数 | 结果 |
|---|---|---|
| ∀ n, n²+n 为偶数 | 2 | 通过（第 1 轮 `.mp` 用反，第 2 轮 `.mpr` 修正） |
| ∀ p 素数, ∃ n:ℝ, n > p | 1 | 通过 |

验证判据：退出码 0、输出无 `error:`、`#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`、无 `sorryAx`。

## 复现

```bash
# 方式一：从 wheel 安装并自举环境
pip install lean_auto-0.2.0-py3-none-any.whl
lean-auto setup && source ~/.lean-auto/env.sh

# 方式二：已有 Lean + Mathlib
unzip lean-auto.zip && cd lean-auto
export LLM_MODEL=Qwen/Qwen3.5-27B
export OPENAI_BASE_URL=https://api-inference.modelscope.cn/v1
export OPENAI_API_KEY=<你的 key>
export LEAN_CMD="lake env lean"
export LEAN_CWD=/path/to/mathlib
python3 -m lean_auto run --problem examples/even-sq/problem.json --max-attempts 3
python3 -m lean_auto run --problem examples/prime-gt/problem.json --max-attempts 3
```
