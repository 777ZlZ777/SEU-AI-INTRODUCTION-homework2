# 63026201-吴雨鸥

## 第二次作业：Euclid 定理的 Lean 形式化证明

> 题目：对任意正整数 n，都存在素数 p > n。
> 本作业设计一个能自主调用 Lean 编译器验证的 Agent，完成该定理的形式化证明。

### 文件清单

| 文件 | 说明 |
|---|---|
| `63026201吴雨鸥第二次作业.pdf` | **一页 A4 总结报告**（主交付物）：问题描述、证明思路、Lean 代码、Agent 架构图、真机验证结果 |
| `人工智能导论第二次作业_吴雨鸥_63026201.html` | 上述报告的 HTML 源文件 |
| `proof/Euclid.lean` | 最终通过编译的 Lean 4 证明（3 个定理） |
| `proof/lakefile.toml`、`proof/lean-toolchain` | 独立下游工程配置（`require mathlib @ v4.35.0`） |
| `proof/verify.sh` | 一键复现脚本：`lake build Euclid` + `#check` + `#print axioms` |
| `proof/VERIFY.md` | 真机验证记录：命令、输出、踩过的坑、所依赖的 mathlib 定理清单 |
| `agent/DESIGN.md` | Agent 设计文档：架构（感知→规划→行动→验证→反思）、工具集、错误分类→修复策略表、本次运行实录 |
| `agent/proof_agent.py` | 可运行的 Agent 验证/修复循环 harness（诊断解析、快照、报告） |

### 核心结论

形式化目标（比题面更强，覆盖全部自然数）：

```lean
theorem exists_prime_gt (n : ℕ) : ∃ p, n < p ∧ Nat.Prime p
```

证明思路为 Euclid 的阶乘构造：取 `m = n! + 1`，令 `p = m.minFac`。
若 `p ≤ n` 则 `p ∣ n!`，又 `p ∣ n! + 1`，故 `p ∣ 1`，与「素数不整除 1」矛盾，因此 `n < p`。

### 验证环境与结果

- Lean 4.35.0 + mathlib v4.35.0（Windows 11）
- `lake build Euclid` → Build completed successfully (9047 jobs)，零 error、零 warning
- `#print axioms` → 仅依赖 `propext`、`Classical.choice`、`Quot.sound`，**未使用 `sorry`**
- Agent harness 实测：`--- attempt 1: PASS (24.6s) ---`，1 轮通过

### 复现方式

```bash
# 需要 Lean 4.35.0 与 mathlib v4.35.0 源码
cd proof
MATHLIB=/path/to/mathlib ./verify.sh
```

详见 `proof/VERIFY.md`。
