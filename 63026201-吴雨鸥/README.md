# 63026201-吴雨鸥

## 第二次作业：Euclid 定理的 Lean 形式化证明

> 题目：对任意正整数 n，都存在素数 p > n。
> 本作业设计一个能自主调用 Lean 编译器验证的 Agent，完成该定理的形式化证明。

### 提交文件

| 文件 | 说明 |
|---|---|
| `63026201吴雨鸥第二次作业.pdf` | 一页 A4 总结，含问题描述、证明思路、Lean 代码、Agent 架构图与真机验证结果 |

### 核心结论

形式化目标（比题面更强，覆盖全部自然数）：

```lean
theorem exists_prime_gt (n : ℕ) : ∃ p, n < p ∧ Nat.Prime p
```

证明思路为 Euclid 的阶乘构造：取 `m = n! + 1`，令 `p = m.minFac`。
若 `p ≤ n` 则 `p ∣ n!`，又 `p ∣ n! + 1`，故 `p ∣ 1`，与「素数不整除 1」矛盾，因此 `n < p`。

### 验证环境

- Lean 4.35.0 + mathlib v4.35.0（Windows）
- `lake build Euclid` → Build completed successfully，零 error、零 warning
- `#print axioms` → 仅依赖 `propext`、`Classical.choice`、`Quot.sound`，未使用 `sorry`
