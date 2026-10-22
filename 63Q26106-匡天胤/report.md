# Lean 4 + 大模型自动定理证明：两道数学命题的机器验证实验

**匡天胤 63Q26106 ｜ 2026-10-23**

## 一、方法

固定提示词让大模型输出完整 Lean 4 代码（以 `import Mathlib` 开头、声明原样照抄、禁用 `sorry`/`admit`/`axiom`、末尾 `#print axioms`）。代码先过静态闸门，再交 Lean 4.36 + Mathlib 真编译，最后审计公理：只允许 `propext`、`Classical.choice`、`Quot.sound`，出现 `sorryAx` 即判失败。失败时把完整代码与报错原文回灌，最多 3 轮。

模型：`Qwen3.5-27B`（温度 0）。

## 二、结果

| 命题 | 轮数 | Lean 耗时 | 判定 | 公理 |
|---|---|---|---|---|
| ∀ n : Nat, Even (n²+n) | 2 | 9.9 s | 通过 | 3 条 |
| ∀ p prime, ∃ n : Real, n > p | 1 | 5.2 s | 通过 | 3 条 |

## 三、关键代码与验证输出

### ① ∀ n, n²+n 为偶数

第 1 轮把 `Nat.even_mul` 的方向用反（`.mp`），Lean 报类型不匹配；第 2 轮改 `.mpr` 通过。

```lean
theorem even_sq_add_self (n : ℕ) : Even (n ^ 2 + n) := by
  rw [show n ^ 2 + n = n * (n + 1) by ring]
  apply Nat.even_mul.mpr      -- round 1 used .mp (wrong direction)
  ...
#print axioms even_sq_add_self
```

```
'even_sq_add_self' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ② ∀ p 素数, ∃ n:ℝ, n > p

一轮通过：

```lean
theorem exists_real_gt_prime (p : ℕ) (hp : p.Prime) :
    ∃ n : ℝ, (n : ℝ) > p := by
  use (p : ℝ) + 1
  apply lt_add_of_pos_right
  norm_num
```

## 四、失败回灌实例（第 1 题第 1 轮，Lean 原文节选）

```
Tactic `apply` failed: could not unify the conclusion of
`Nat.even_mul.mp`  Even ?a ∨ Even ?b  with the goal  Even (n * (n + 1))
```

报错与上一轮完整代码一起回灌，模型据此把 `.mp` 改成 `.mpr`，第 2 轮通过。

## 五、结论

两道命题均通过真实 Lean + Mathlib 验证，公理依赖仅三条标准公理，无 `sorryAx`。第 1 题第 1 轮的失败与第 2 轮的修正说明：大模型负责生成，Lean 负责裁决，错误会被精确定位并回灌。对照组本地 4B 模型在同一流水线上 3 轮全败（臆造引理、重复错误），说明瓶颈在模型能力，而非验证流程。

源码与运行记录：`lean-auto.zip`（内含 `lean_auto/`、`tests/`、`examples/`、`docker/`、README 与验收报告）。
