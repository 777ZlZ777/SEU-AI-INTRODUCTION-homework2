# Euclid 定理 —— 真机验证记录

## 环境

| 组件 | 版本 / 位置 |
|---|---|
| Lean | **4.35.0**（`~/.elan/toolchains/leanprover--lean4---v4.35.0`） |
| Lake | 5.0.0 |
| mathlib4 | **v4.35.0**（本地源码 `../_toolchain/mathlib4`，含 9031 个预编译 olean） |
| OS | Windows 11 x86_64 |

## 结论

```
$ lake build Euclid
✔ [9046/9047] Built Euclid (22s)
Build completed successfully (9047 jobs).
rc=0
```

**零 error、零 warning，未使用 `sorry`。**

## 被验证的定理（`#check` 实输出）

```
Euclid.exists_prime_gt           (n : ℕ) : ∃ p, n < p ∧ Nat.Prime p
Euclid.exists_prime_gt_pos       (n : ℕ) (_hn : 0 < n) : ∃ p, n < p ∧ Nat.Prime p
Euclid.exists_prime_gt_of_mathlib (n : ℕ) : ∃ p, n < p ∧ Nat.Prime p
```

公理依赖（`#print axioms`，无多余公理、无 sorry）：

```
'Euclid.exists_prime_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 复现步骤

```bash
cd 63026201-吴雨鸥/proof
./verify.sh
```

脚本做的事：把 `Euclid.lean` 拷进 mathlib 工程根 → `lake build Euclid` →
用一份临时 `Check.lean` 做 `#check` 与 `#print axioms`。

手动等价命令：

```bash
export PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH"
cd /path/to/mathlib            # mathlib v4.35.0 源码
cp .../63026201-吴雨鸥/proof/Euclid.lean Euclid.lean
printf '\nlean_lib Euclid where\n  roots := #[`Euclid]\n' >> lakefile.lean   # 只做一次
lake build Euclid
printf 'import Euclid\n#check Euclid.exists_prime_gt\n#print axioms Euclid.exists_prime_gt\n' > Check.lean
lake env lean Check.lean
```

> 说明：本机把 mathlib 以**源码**方式挂载（`人工智能作业2/_toolchain/mathlib4`），
> 所以直接在 mathlib 工程里编译。
> 若你有自己的下游工程，`lakefile.toml` 里 `require mathlib @ v4.35.0` 即可，
> 证明代码无需任何改动。

## 踩过的三个坑（真实轨迹）

1. **模块系统**：mathlib v4.35 开了 `requiresModuleSystem`。
   只加 `module` 头还不够 —— 声明必须放进 **`public section`**，否则会被写进
   `Euclid.olean.private`，下游 `import Euclid` 拿不到（`#check` 报 unknown identifier）。
   而标了 `public` 之后，签名里用到的常量又必须 **`public import`** 进来，
   否则报 `A public declaration Nat.Prime exists but is imported privately`。
   → 最终解法：`module` + `public import Mathlib` + `public section`。

2. **`lake build <模块名>` 需要目标登记**：mathlib 的 lakefile 只声明了 `Mathlib` 等库，
   直接 `lake build Euclid` 会报 `unknown target 'Euclid'`。
   → 在 lakefile 末尾补一行 `lean_lib Euclid where roots := #[`Euclid]`。
   （`lake env lean Euclid.lean` 可以绕过，但它不产出 olean，只做检查。）

3. **Lean/Std 核心库没有 `Nat.Prime` / `Nat.factorial` / `Nat.minFac`**
   （`#check` 全部 unknown constant），所以这个定理**必须**依赖 mathlib，无法零依赖证明。

## 依赖的 mathlib 定理（均已 grep 源码确认签名）

| 用途 | 定理 | 定义位置 |
|---|---|---|
| `0 < n!` | `Nat.factorial_pos` | `Mathlib/Data/Nat/Factorial/Basic.lean:69` |
| `Prime (minFac m)` | `Nat.minFac_prime` | `Mathlib/Data/Nat/Prime/Defs.lean:286` |
| `minFac m ∣ m` | `Nat.minFac_dvd` | `Mathlib/Data/Nat/Prime/Defs.lean:283` |
| `p ≤ n → p ∣ n!` | `Nat.dvd_factorial` | `Mathlib/Data/Nat/Factorial/Basic.lean:82` |
| `p ∣ n! → (p ∣ n!+1 ↔ p ∣ 1)` | `Nat.dvd_add_iff_right` | 用法见 `Mathlib/Data/Nat/Prime/Infinite.lean:43` |
| `Prime p → ¬ p ∣ 1` | `Nat.Prime.not_dvd_one` | `Mathlib/Data/Nat/Prime/Defs.lean:191` |

结构上与本证明完全一致的官方写法，见 `Mathlib/Data/Nat/Prime/Infinite.lean:36-45`
（`Nat.exists_infinite_primes`，给出的是 `p ≥ n`；本定理用反证直接得到严格的 `n < p`）。
