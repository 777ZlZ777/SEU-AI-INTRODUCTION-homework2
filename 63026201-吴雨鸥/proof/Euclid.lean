/-
  Euclid's theorem  ——  对任意正整数 n，存在素数 p > n
  ======================================================

  我们证明更强的版本：对任意自然数 n（因而也对任意正整数 n），
  存在素数 p 满足 n < p。

  构造（Euclid 的阶乘形式）：
    取 m := n! + 1。
    因为 n! > 0，所以 1 < m，特别地 m ≠ 1；
    于是 m 的最小因子 p := m.minFac 是素数，且 p ∣ m。
    若反设 p ≤ n，则 p 是 ≤ n 的正数，故 p ∣ n!（Nat.dvd_factorial）；
    又 p ∣ n! + 1，于是 p ∣ 1（Nat.dvd_add_iff_right）；
    但素数不整除 1（Nat.Prime.not_dvd_one），矛盾。故 n < p。
-/

module

-- mathlib 开启了模块系统（requiresModuleSystem）：
--   * 文件需要 `module` 头；
--   * 对外可见的声明要放进 `public section`；
--   * 这些声明的签名里用到的常量必须 `public import` 进来。
public import Mathlib

public section

namespace Euclid

/-- 主定理：Euclid 定理，阶乘构造法。 -/
theorem exists_prime_gt (n : ℕ) : ∃ p, n < p ∧ Nat.Prime p := by
  let m := n.factorial + 1
  -- 1 < m，因为 n! > 0
  have hm_gt_one : 1 < m := by
    simpa [m] using Nat.succ_lt_succ (Nat.factorial_pos n)
  have hm_ne_one : m ≠ 1 := ne_of_gt hm_gt_one
  -- p 是 m 的最小因子
  let p := m.minFac
  have hp_prime : Nat.Prime p := by
    simpa [p] using Nat.minFac_prime hm_ne_one
  have hp_dvd_m : p ∣ m := by
    simpa [p] using Nat.minFac_dvd m
  -- 关键一步：p > n（反证）
  have hnp : n < p := by
    by_contra h
    have hp_le_n : p ≤ n := le_of_not_gt h
    -- 若 p ≤ n，则 p 整除 n!
    have hp_dvd_fact : p ∣ n.factorial := Nat.dvd_factorial hp_prime.pos hp_le_n
    have hp_dvd_m' : p ∣ n.factorial + 1 := by
      simpa [m] using hp_dvd_m
    -- 又 p ∣ n! + 1，故 p ∣ 1
    have hp_dvd_one : p ∣ 1 := (Nat.dvd_add_iff_right hp_dvd_fact).2 hp_dvd_m'
    -- 素数不整除 1，矛盾
    exact hp_prime.not_dvd_one hp_dvd_one
  exact ⟨p, hnp, hp_prime⟩

/-- 另一种写法：直接复用 mathlib 的 `Nat.exists_infinite_primes`（它给出 p ≥ n）。 -/
theorem exists_prime_gt_of_mathlib (n : ℕ) : ∃ p, n < p ∧ Nat.Prime p := by
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (n + 1)
  exact ⟨p, Nat.lt_of_succ_le hp_ge, hp_prime⟩

/-- 题面形式：正整数 n（0 < n）之上必有素数。 -/
theorem exists_prime_gt_pos (n : ℕ) (_hn : 0 < n) : ∃ p, n < p ∧ Nat.Prime p :=
  exists_prime_gt n

end Euclid
