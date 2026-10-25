/-
Copyright: 无
-/

/-!
# 连续函数在 `[a, +∞)` 上有界

设 `f : ℝ → ℝ` 在 `[a, +∞)` 上连续，且当 `x → +∞` 时 `f x` 有有限极限 `L`。
证明 `f` 在 `[a, +∞)` 上有界。

证明分三步：

1. 由极限的 `ε`–`N` 定义（取 `ε = 1`），存在 `R`，使得 `x ≥ R` 时 `|f x - L| < 1`，
   于是 `|f x| ≤ |f x - L| + |L| < 1 + |L|`。
2. 取 `b = max a R`。闭区间 `[a, b]` 是紧集，`f` 在其上连续，故由最值定理
   取到最大值点 `xm` 与最小值点 `xn`，从而 `x ∈ [a, b]` 时
   `|f x| ≤ max {|f xm|, |f xn|}`。
3. 取

     `M = max (max |f xm| |f xn|) (|L| + 1)`，

   对任意 `x ≥ a` 分 `x ≤ b` 与 `x ≥ b` 两种情形，分别用第 2 步与第 1 步的界。

注：本文件中的引理名与签名按当前 Mathlib（`master`）核对过。闭区间紧性的引理
已移入命名空间，故写作 `ConditionallyCompleteLinearOrder.isCompact_Icc`；
若你的 Mathlib 版本仍保留根命名空间的 `isCompact_Icc`，可直接替换（见下方注释）。
-/

import Mathlib

open Filter Topology

/-- 设 `f : ℝ → ℝ` 在 `[a, +∞)` 上连续，且当 `x → +∞` 时 `f x` 有有限极限 `L`。
则 `f` 在 `[a, +∞)` 上有界。 -/
theorem bounded_on_Ici_of_tendsto_atTop
    {f : ℝ → ℝ} {a L : ℝ}
    (hcont : ContinuousOn f (Set.Ici a))
    (hlim : Tendsto f atTop (𝓝 L)) :
    ∃ M : ℝ, ∀ x : ℝ, a ≤ x → |f x| ≤ M := by
  -- ① 极限的 ε–N 定义，取 ε = 1：存在 R，使 x ≥ R 时 |f x - L| < 1
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 hlim 1 zero_lt_one
  -- ② 取 b = max a R，在紧区间 [a, b] 上用最值定理
  let b : ℝ := max a R
  have hab : a ≤ b := le_max_left a R
  have hRb : R ≤ b := le_max_right a R
  have hne : (Set.Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
  have hcont' : ContinuousOn f (Set.Icc a b) :=
    hcont.mono fun x hx => hx.1
  have hcomp : IsCompact (Set.Icc a b) :=
    ConditionallyCompleteLinearOrder.isCompact_Icc a b
    -- 旧版本 Mathlib 可换成：isCompact_Icc
  obtain ⟨xm, _, hxmax⟩ := hcomp.exists_isMaxOn hne hcont'
  obtain ⟨xn, _, hxmin⟩ := hcomp.exists_isMinOn hne hcont'
  -- ③ 整体界 = max{ [a,b] 上的界, 尾部的界 }
  refine ⟨max (max |f xm| |f xn|) (|L| + 1), ?_⟩
  intro x hx
  by_cases hxb : x ≤ b
  · -- 情形一：x ∈ [a, b]，用最大值、最小值夹住
    have hxI : x ∈ Set.Icc a b := ⟨hx, hxb⟩
    have hle : f x ≤ f xm := (isMaxOn_iff.1 hxmax) x hxI
    have hge : f xn ≤ f x := (isMinOn_iff.1 hxmin) x hxI
    have h1 : f x ≤ max |f xm| |f xn| :=
      le_trans hle (le_trans (le_abs_self _) (le_max_left _ _))
    have h2 : -max |f xm| |f xn| ≤ f x := by
      have h3 : -f x ≤ |f xn| :=
        le_trans (neg_le_neg hge) (neg_le_abs _)
      have h4 : |f xn| ≤ max |f xm| |f xn| := le_max_right _ _
      linarith
    exact le_trans (abs_le.2 ⟨h2, h1⟩) (le_max_left _ _)
  · -- 情形二：x ≥ b ≥ R，用尾部估计
    push_neg at hxb
    have hRx : R ≤ x := le_trans hRb (le_of_lt hxb)
    have hdist : dist (f x) L < 1 := hR x hRx
    have habs : |f x - L| < 1 := by
      rwa [Real.dist_eq] at hdist
    have htail : |f x| ≤ |L| + 1 := by
      calc
        |f x| = dist (f x) 0 := by simp [Real.dist_eq]
        _ ≤ dist (f x) L + dist L 0 := dist_triangle _ _ _
        _ = |f x - L| + |L| := by simp [Real.dist_eq]
        _ ≤ 1 + |L| := by linarith
        _ = |L| + 1 := by ring
    exact le_trans htail (le_max_right _ _)
