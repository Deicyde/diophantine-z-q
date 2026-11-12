import Mathlib
/-!
rv-leaves-a: a normalization-robust form of pkg-I5's F3 bookkeeping.

`PazukiGoodGenus2` and glue-assembly's `PazukiOutput` shift the Faltings height by `log π`
(Faltings' `(i/2)^g` normalization → Deligne's `(i/2π)^g`, `(g/2) log π` at `g = 2`). If Pazuki's
normalization were a larger shift (any shift `s ≤ 3`), the leaf with `log π` would be stronger than
published. The hardened leaf uses `X = max(1, h_F + 3)`, which is a consequence of Pazuki's bound for
every shift `s ≤ 3` (the right side is monotone in `X`), and `f3_numerics_robust` shows that the
downstream constant `10000·2²⁴` is unchanged. So the hardening is free.
-/
namespace RvLeavesA
open Real

noncomputable def pazukiC2 : ℝ := 1000 * 2 ^ 4 * (Real.log (2 ^ 4)) ^ 5

/-- Monotonicity: Pazuki's bound at a shift `s ≤ 3` implies the bound at shift `3`. -/
theorem pazuki_shift_mono {hF hθ s : ℝ} (hs : s ≤ 3)
    (hP : hθ ≤ max 1 (hF + s) / 2 + pazukiC2 * Real.log (max 1 (hF + s) + 2)) :
    hθ ≤ max 1 (hF + 3) / 2 + pazukiC2 * Real.log (max 1 (hF + 3) + 2) := by
  have hX : max 1 (hF + s) ≤ max 1 (hF + 3) := max_le_max le_rfl (by linarith)
  have h0 : 0 < max 1 (hF + s) + 2 := by linarith [le_max_left 1 (hF + s)]
  have hC0 : 0 ≤ pazukiC2 := by unfold pazukiC2; positivity
  have hl : Real.log (max 1 (hF + s) + 2) ≤ Real.log (max 1 (hF + 3) + 2) :=
    Real.log_le_log h0 (by linarith)
  calc hθ ≤ _ := hP
    _ ≤ _ := by gcongr

/-- `log π ≤ 3`, so the published-normalization (Deligne) form implies the hardened form. -/
theorem log_pi_le_three : Real.log Real.pi ≤ 3 := by
  have h4 : Real.log Real.pi ≤ Real.log 4 :=
    Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])
  have h42 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_lt_d9]

/-- F3 bookkeeping from the hardened bound: same constant `10000·2²⁴` as `f3_numerics`. -/
theorem f3_numerics_robust {hF hθ : ℝ}
    (hP : hθ ≤ max 1 (hF + 3) / 2 + pazukiC2 * Real.log (max 1 (hF + 3) + 2)) :
    hθ ≤ 10000 * 2 ^ 24 * max 1 hF := by
  set X := max 1 hF with hX
  set XD := max 1 (hF + 3) with hXD
  have hX1 : 1 ≤ X := le_max_left _ _
  have hXD1 : 1 ≤ XD := le_max_left _ _
  have hXD4 : XD ≤ 4 * X := by
    refine max_le (by linarith) ?_
    linarith [le_max_right 1 hF]
  have hlog2 : Real.log (XD + 2) ≤ 2 * XD := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < XD + 2)
    linarith
  have hC2 : pazukiC2 ≤ 1000 * 2 ^ 24 := by
    have hl : Real.log (2 ^ 4 : ℝ) ≤ 15 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2 ^ 4)
      linarith [show ((2 : ℝ) ^ 4) = 16 by norm_num]
    have hl0 : 0 ≤ Real.log (2 ^ 4 : ℝ) := Real.log_nonneg (by norm_num)
    have : (Real.log (2 ^ 4 : ℝ)) ^ 5 ≤ 15 ^ 5 := pow_le_pow_left₀ hl0 hl 5
    unfold pazukiC2
    nlinarith
  have hC0 : 0 ≤ pazukiC2 := by unfold pazukiC2; positivity
  have hlogXD : 0 ≤ Real.log (XD + 2) := Real.log_nonneg (by linarith)
  calc hθ ≤ XD / 2 + pazukiC2 * Real.log (XD + 2) := hP
    _ ≤ XD / 2 + 1000 * 2 ^ 24 * (2 * XD) := by gcongr
    _ ≤ 10000 * 2 ^ 24 * X := by nlinarith

/-- The original (log π) form implies the hardened form, so nothing downstream is lost. -/
theorem f3_numerics_of_logpi {hF hθ : ℝ}
    (hP : hθ ≤ max 1 (hF + Real.log Real.pi) / 2 +
      pazukiC2 * Real.log (max 1 (hF + Real.log Real.pi) + 2)) :
    hθ ≤ 10000 * 2 ^ 24 * max 1 hF :=
  f3_numerics_robust (pazuki_shift_mono log_pi_le_three hP)

end RvLeavesA
#print axioms RvLeavesA.f3_numerics_robust
#print axioms RvLeavesA.f3_numerics_of_logpi
