import ZInQKernel.Contrib.TYZDecomp.Leaves
import ZInQKernel.Contrib.HeckeAll.Continuation
import ZInQKernel.Contrib.GaussFE.FunctionalEquation5

/-!
# tyz-lcal: an explicit bound for `L(C₁, 1)` (draft; merged into `TYZLcal.lean`)
-/

noncomputable section

namespace ZInQ.Contrib.TYZLcal

open Complex Real Set MeasureTheory HurwitzZeta ZInQ.Contrib.HeckeFE

/-! ## §1. `Λ(1)` as two integrals over `(1, ∞)` -/

theorem integrableOn_gaussTheta (a b : UnitAddCircle) : IntegrableOn (gaussTheta a b) (Ioi 0) := by
  have h := mellinConvergent_gaussTheta a b 1
  simpa [MellinConvergent] using h

/-- `Λ_{a,b}(1) = ∫₁^∞ θ_{a,b} + ∫₁^∞ θ^dual_{a,b}` (split at `1`, substitute `x ↦ 1/x` on `(0, 1)`). -/
theorem gaussLambda_one_eq (a b : UnitAddCircle) :
    gaussLambda a b 1 = (∫ x in Ioi 1, gaussTheta a b x) + ∫ x in Ioi 1, gaussThetaDual a b x := by
  have hint := integrableOn_gaussTheta a b
  have h1 : gaussLambda a b 1 = ∫ x in Ioi 0, gaussTheta a b x := by
    simp [gaussLambda, mellin]
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ici 1) := by
    rw [Set.disjoint_iff]; rintro x ⟨⟨-, hx⟩, hx'⟩; exact absurd hx' (not_le.mpr hx)
  rw [h1, ← Ioo_union_Ici_eq_Ioi zero_lt_one,
    setIntegral_union hdisj measurableSet_Ici (hint.mono_set Ioo_subset_Ioi_self)
      (hint.mono_set (Ici_subset_Ioi.mpr zero_lt_one)),
    integral_Ici_eq_integral_Ioi, add_comm]
  congr 1
  -- the substitution
  set f : ℝ → ℂ := (Ioo (0 : ℝ) 1).indicator (gaussTheta a b) with hf
  have e1 : ∫ x in Ioo 0 1, gaussTheta a b x = mellin f 1 := by
    simp only [mellin, sub_self, cpow_zero, one_smul, hf]
    rw [setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Ioi_self]
  have e2 : mellin f 1 = mellin (fun t => f t⁻¹) (-1) := by
    rw [← mellin_comp_inv]; simp
  rw [e1, e2, mellin]
  have e3 : ∫ x in Ioi (1 : ℝ), gaussThetaDual a b x =
      ∫ x in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator (gaussThetaDual a b) x := by
    rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.mpr
      (Ioi_subset_Ioi zero_le_one)]
  rw [e3]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [hf]
  by_cases h1t : 1 < t
  · have hmem : t⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr ht, inv_lt_one_of_one_lt₀ h1t⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show t ∈ Ioi (1:ℝ) from h1t),
      ← one_div, gaussTheta_one_div a b ht, smul_eq_mul, ← mul_assoc]
    have : (t : ℂ) ^ ((-1 : ℂ) - 1) * ((t ^ (2 : ℝ) : ℝ) : ℂ) = 1 := by
      rw [show (-1 : ℂ) - 1 = -((2 : ℝ) : ℂ) by norm_num, cpow_neg,
        ← ofReal_cpow ht.le, inv_mul_cancel₀]
      exact ofReal_ne_zero.mpr (rpow_pos_of_pos ht _).ne'
    rw [this, one_mul]
  · have hmem : t⁻¹ ∉ Ioo (0 : ℝ) 1 := fun h => h1t ((inv_lt_one₀ ht).mp h.2)
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show t ∉ Ioi (1:ℝ) from h1t),
      smul_zero]

/-! ## §2. Integrals of exponentially decaying functions over `(1, ∞)` -/

theorem integral_exp_decay {C c : ℝ} (hc : 0 < c) :
    ∫ x in Ioi (1 : ℝ), C * Real.exp (-c * (x - 1)) = C / c := by
  have h : ∀ x : ℝ, C * Real.exp (-c * (x - 1)) = (C * Real.exp c) * Real.exp (-c * x) := by
    intro x; rw [mul_assoc, ← Real.exp_add]; ring_nf
  simp_rw [h]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -c < 0)]
  rw [mul_one, neg_div_neg_eq, mul_div_assoc', mul_assoc, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, mul_one]

theorem integrableOn_exp_decay (C : ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => C * Real.exp (-c * (x - 1))) (Ioi 1) := by
  have h : ∀ x : ℝ, C * Real.exp (-c * (x - 1)) = (C * Real.exp c) * Real.exp (-c * x) := by
    intro x; rw [mul_assoc, ← Real.exp_add]; ring_nf
  simp_rw [h]
  exact (integrableOn_exp_mul_Ioi (by linarith : -c < 0) 1).const_mul _

/-- If `‖f x‖ ≤ C e^{−c(x−1)}` on `(1, ∞)` then `‖∫₁^∞ f‖ ≤ C/c`. -/
theorem norm_integral_Ioi_one_le {f : ℝ → ℂ} {C c : ℝ} (hc : 0 < c)
    (hf : ∀ x : ℝ, 1 < x → ‖f x‖ ≤ C * Real.exp (-c * (x - 1))) :
    ‖∫ x in Ioi (1 : ℝ), f x‖ ≤ C / c := by
  rw [← integral_exp_decay (C := C) hc]
  refine norm_integral_le_of_norm_le (integrableOn_exp_decay C hc) ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => hf x hx)

end ZInQ.Contrib.TYZLcal
