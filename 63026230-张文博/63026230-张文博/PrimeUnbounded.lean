import Mathlib

/-!
# Euclid 定理：素数没有上界

对任意自然数 n，都存在素数 p > n。
思路：取 N = n! + 1，设 p 为 N 的素因子；
若 p ≤ n，则 p ∣ n!，与 p ∣ n! + 1 相减得 p ∣ 1，矛盾。
-/

theorem exists_prime_gt (n : ℕ) : ∃ p, p.Prime ∧ n < p := by
  obtain ⟨p, hp, hdvd⟩ :=
    Nat.exists_prime_and_dvd (show 1 < n ! + 1 by
      have := Nat.factorial_pos n; omega)
  refine ⟨p, hp, ?_⟩
  by_contra h
  push_neg at h
  have hfac : p ∣ n ! := hp.dvd_factorial.mpr h
  have hone : p ∣ 1 := by
    have := Nat.dvd_sub hdvd hfac (Nat.le_succ (n !))
    simpa using this
  exact hp.not_dvd_one hone

-- 一行库解交叉校验（Mathlib 已内置该结论）
example (n : ℕ) : ∃ p, p.Prime ∧ n < p := by
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (n + 1)
  exact ⟨p, hpp, by omega⟩

#print axioms exists_prime_gt
