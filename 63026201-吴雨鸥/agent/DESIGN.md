# LeanTheoremAgent —— 一个会自己跑编译器验证的形式化证明 Agent

> 目标命题：**Euclid 定理** —— 对任意正整数 `n`，存在素数 `p > n`。
> 形式化目标：`theorem exists_prime_gt (n : ℕ) : ∃ p, n < p ∧ Nat.Prime p`

---

## 1. 设计原则

| 原则 | 含义 |
|---|---|
| **编译器是唯一裁判** | 不接受"看起来对"的证明。唯一成功条件是 `lake build` 零 error、零 sorry。 |
| **先检索再生成** | 写证明前先确认定理名/签名是否存在（grep 源码 / `#check`），杜绝凭记忆编 API。 |
| **最小变更迭代** | 每轮只针对当前报错改一处，保留全部历史快照，便于回溯。 |
| **有预算、会认输** | 迭代有上限；卡住时输出"卡点报告"（剩余目标 + 已确认可用的定理），而不是无限试。 |
| **能降级** | 高级定理走不通时，退回到更初等/更长但可控的构造。 |

---

## 2. 架构：感知 → 规划 → 行动 → 验证 → 反思

```
            ┌──────────────────────────────────────────┐
   命题 ──▶ │ Planner   数学草图 → Lean 骨架 → 子目标列表 │
            └───────────────┬──────────────────────────┘
                            ▼
            ┌──────────────────────────────────────────┐
            │ Retriever  定理库检索（grep / #check /     │
            │            #find / LeanSearch）           │
            └───────────────┬──────────────────────────┘
                            ▼
            ┌──────────────────────────────────────────┐
            │ Writer     生成/修补候选 Lean 代码          │
            └───────────────┬──────────────────────────┘
                            ▼
                  Verifier  lake build / lean
                            │
                  ┌─────────┴─────────┐
              通过 │                   │ 有 error
                  ▼                   ▼
              输出证明        ┌──────────────────┐
              + 报告          │ Critic  错误分类   │
                             │ Repairer 修复策略  │
                             └────────┬─────────┘
                                      │ 回到 Writer（轮次 +1）
```

---

## 3. 工具集（ToolSet）

| 工具 | 作用 | 实现 |
|---|---|---|
| `lake_build(project, target)` | 编译，返回原始 diagnostics | `subprocess`，见 `proof_agent.py` |
| `lean_probe(consts[])` | 用 `#check` 批量确认常量名与签名 | 生成临时 `.lean` 后 `lean` |
| `grep_theorem(pattern, root)` | 在 mathlib 源码里搜定理定义/用法 | ripgrep |
| `read_source(path, lines)` | 读某个 mathlib 文件，学官方写法 | 文件读取 |
| `apply_patch(file, old, new)` | 最小改动写回 | 文件写入 |
| `snapshot(attempt, content)` | 每轮快照到 `.attempts/` | 文件写入 |
| `web_search(query)` | 找不到定理时的兜底 | 外部搜索（可选） |

---

## 4. 反思闭环（核心）

```python
for attempt in range(1, MAX_ATTEMPTS + 1):
    write(file, candidate)
    diagnostics = lake_build()                 # 唯一的裁判
    if not diagnostics.errors:
        return Verified(candidate, report)     # 成功
    plan = critic(diagnostics)                 # 分类 + 定位到行
    if plan.repeated(3):                       # 同类错误连出 3 次
        plan = escalate(plan)                  # 换定理 / 换构造 / 拆分引理
    candidate = repairer(candidate, plan)
return StuckReport(diagnostics, confirmed_theorems)
```

### 错误分类 → 修复策略表

| Lean 报错 | 类型 | 修复动作 |
|---|---|---|
| `unknown constant 'Nat.foo'` | 名字错/不存在 | `grep_theorem` 找真名；找不到就换定理或自己证引理 |
| `application type mismatch` | 参数顺序/隐式参数错 | `#check` 打印签名后对齐参数 |
| `type mismatch` | 类型不一致 | 加 `simpa [...] using`、`norm_num`、`exact_mod_cast` |
| `unsolved goals` | 洞没填上 | 补 `have` 中间断言；换 `omega` / `linarith` / `nlinarith` / `ring_nf` |
| `tactic 'omega' failed` | 算术前提不足 | 把缺失的不等式先证出来再调 `omega` |
| `failed to synthesize OfNat` | 类型推导歧义 | 显式加类型标注 `(n : ℕ)` |
| `declaration uses 'sorry'` | 假证明 | 直接判失败（本项目禁止 sorry） |
| `heartbeats` / 超时 | 项太大 | 拆成子引理、加 `simp` 中间步骤 |

---

## 5. 本次命题的具体计划（Euclid 定理）

**数学草图（Planner 的输出）**

1. 取 `m := n! + 1`；
2. `n! > 0` ⟹ `m ≠ 1`；
3. 令 `p := m.minFac`，则 `Nat.Prime p` 且 `p ∣ m`；
4. 反设 `p ≤ n`，则 `p ∣ n!`（`Nat.dvd_factorial`）；
5. 又 `p ∣ n! + 1`，故 `p ∣ 1`（`Nat.dvd_add_iff_right`）；
6. 素数不整除 1（`Nat.Prime.not_dvd_one`），矛盾 ⟹ `n < p`。

**子目标 → Lean 常量映射（Retriever 已核实）**

| 子目标 | 定理 | 出处 |
|---|---|---|
| `0 < n!` | `Nat.factorial_pos` | `Mathlib/Data/Nat/Factorial/Basic.lean:69` |
| `Prime (minFac m)` | `Nat.minFac_prime` | `Mathlib/Data/Nat/Prime/Defs.lean:286` |
| `minFac m ∣ m` | `Nat.minFac_dvd` | `Mathlib/Data/Nat/Prime/Defs.lean:283` |
| `p ≤ n → p ∣ n!` | `Nat.dvd_factorial` | `Mathlib/Data/Nat/Factorial/Basic.lean:82` |
| `p ∣ n! → (p ∣ n!+1 ↔ p ∣ 1)` | `Nat.dvd_add_iff_right` | `Mathlib/Data/Nat/GCD/Basic.lean:248` 用法 |
| `Prime p → ¬ p ∣ 1` | `Nat.Prime.not_dvd_one` | `Mathlib/Data/Nat/Prime/Defs.lean:191` |

**降级路径**：若 `minFac` 系列不可用 ⟹ 改用 `Nat.exists_prime_and_dvd` 取素因子；
再不行 ⟹ 直接用 mathlib 已有结论 `Nat.exists_infinite_primes (n+1)`（`n+1 ≤ p` ⟹ `n < p`）。

---

## 6. 预算与停止条件

- `MAX_ATTEMPTS = 8`，每轮最小变更；
- 同类错误连续 3 次 ⟹ 升级策略（escalate）；
- 卡住退出时产出 **卡点报告**：未解决 goals + 已核实定理清单 + 各轮快照路径。

---

## 7. 真机运行实录（本次 Euclid 定理）

| 轮次 | 动作 | 编译器反馈 | Agent 的应对 |
|---|---|---|---|
| 0 | Retriever：grep mathlib 源码核实 6 个定理名 | — | 与官方 `Infinite.lean` 的写法对齐（`.2` 方向、`not_dvd_one`） |
| 1 | Writer 产出第一版 | `warning: missing 'module' header` | 补 `module` 头 |
| 2 | 补 `module` | 编译通过，但下游 `import Euclid` 查不到定理 | 原因：未标 `public` 的声明只进 `.olean.private` → 加 `public section` |
| 3 | 加 `public section` | `A public declaration Nat.Prime exists but is imported privately` | 把 `import Mathlib` 改成 `public import Mathlib` |
| 4 | 三处齐备 | **Build completed successfully (9047 jobs)，零 warning** | 验证完成 |

Agent harness 的实际输出：

```
--- attempt 1: PASS (24.6s) ---
report -> ...\agent\.attempts\report.json
VERIFIED in 1 attempt(s).
```

**三条经验已写回 Retriever 的记忆**：
1. mathlib v4.35 有模块系统：`module` + `public section` + `public import` 三者缺一不可；
2. `lake build <模块>` 需要目标登记（lakefile 里加 `lean_lib`）；
3. `Nat.Prime` / `Nat.factorial` / `Nat.minFac` 只在 mathlib 里，核心库没有 —— 该定理无法零依赖证明。

## 8. 落地文件

- `proof_agent.py` —— 可运行的验证/修复循环（含错误解析、快照、报告）
- `../proof/Euclid.lean` —— 最终通过编译的证明
- `../proof/VERIFY.md` —— 真机验证记录（命令 + 输出）
- `../proof/verify.sh` —— 一键复现脚本
