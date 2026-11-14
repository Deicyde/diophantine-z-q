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


/-! ## §3. The explicit continuation of `L(C₁, s)` and its value at `1` -/

/-- `π^s Γ(s)⁻¹ Λ_{a,b}(s)` is the lattice series for `Re s > 3/2` (proof of
`HeckeFE.gaussL_continuation`). -/
theorem gaussL_eq_of_re (a b : ℝ) {s : ℂ} (hs : 3 / 2 < s.re) :
    (π : ℂ) ^ s * (Gamma s)⁻¹ * gaussLambda a b s = gaussL a b s := by
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hpi : (π : ℂ) ^ s ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero
    (by rintro rfl; norm_num at hs)).mpr (ofReal_ne_zero.mpr pi_ne_zero)
  rw [← (hasSum_gaussLambda a b hs).tsum_eq, gaussL]
  simp_rw [mul_div_assoc]
  rw [tsum_mul_left, cpow_neg]
  field_simp

/-- The explicit continuation of a twisted lattice series (the function of
`HeckeFE.twistedL_continuation`). -/
def Fexp (M : ℕ) (c : ZMod M × ZMod M → ℂ) (s : ℂ) : ℂ :=
  ∑ j : Fin M × Fin M, c (((j.1 : ℤ) : ZMod M), ((j.2 : ℤ) : ZMod M)) *
    ((M : ℂ) / (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ s) *
      ((π : ℂ) ^ s * (Gamma s)⁻¹ *
        gaussLambda (((j.1 : ℝ) / M : ℝ) : UnitAddCircle) (((j.2 : ℝ) / M : ℝ) : UnitAddCircle) s)

theorem differentiable_Fexp (M : ℕ) [NeZero M] (c : ZMod M × ZMod M → ℂ) :
    Differentiable ℂ (Fexp M c) := by
  have hM : (((M : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne M))
  have : NeZero (((M : ℝ) ^ 2 : ℝ) : ℂ) := ⟨hM⟩
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  have : NeZero (π : ℂ) := ⟨hpi⟩
  unfold Fexp
  refine Differentiable.fun_sum fun j _ => ?_
  refine (Differentiable.const_mul ?_ _).mul ?_
  · simp_rw [div_eq_mul_inv, ← cpow_neg]
    exact (differentiable_const_cpow_of_neZero _).comp differentiable_id.neg |>.const_mul _
  · exact ((differentiable_const_cpow_of_neZero (π : ℂ)).mul differentiable_one_div_Gamma).mul
      (differentiable_gaussLambda _ _)

theorem Fexp_eq_twistedL (M : ℕ) [NeZero M] (c : ZMod M × ZMod M → ℂ) {s : ℂ}
    (hs : 3 / 2 < s.re) : Fexp M c s = twistedL M c s := by
  rw [twistedL_eq M c hs, Fexp]
  exact Finset.sum_congr rfl fun j _ => by rw [gaussL_eq_of_re _ _ hs]

/-- The coefficient function of `L(C₁, s)` on `ℤ[i]/4`: `¼ · unitOf`. -/
def cU (x : ZMod 4 × ZMod 4) : ℂ := (1 / 4) * unitOf x

/-- `F₁ := Fexp 4 cU` is the entire continuation of Mathlib's `L(y² = x³ − x, s)`. -/
theorem isLContinuation_Fone : ZInQ.Literature.IsLContinuation (ZInQ.Contrib.TYZDecomp.curveC 1)
    (Fexp 4 cU) := by
  refine ⟨differentiable_Fexp 4 cU, fun s hs => ?_⟩
  have hD1 : DeuringCd 1 := deuringCd_of_gaussPointCount (by norm_num) squarefree_one
    ZInQ.Contrib.GaussFE.gaussPointCount
  rw [Fexp_eq_twistedL 4 cU hs, ZInQ.Contrib.TYZDecomp.curveC,
    ZInQ.Literature.LSeries_cd_eq (by norm_num) squarefree_one s]
  refine (LSeries_eq_twistedL 4 cU _ (fun n hn => ?_) hs).symm
  rw [hD1 n hn, heckeCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [cU, jacobiSym.one_right, Int.cast_one, one_mul]
  ring

/-- **`L(C₁, 1)` as a finite combination of the `Λ_{a,b}(1)`.** -/
theorem lValOne_one_eq : ZInQ.Contrib.TYZDecomp.lValOne 1 =
    ∑ j : Fin 4 × Fin 4, cU (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4)) * (1 / 4) *
      ((π : ℂ) * gaussLambda (((j.1 : ℝ) / 4 : ℝ) : UnitAddCircle) (((j.2 : ℝ) / 4 : ℝ) : UnitAddCircle) 1) := by
  rw [ZInQ.Contrib.TYZDecomp.lValOne_eq isLContinuation_Fone, Fexp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [cpow_one, Complex.Gamma_one, inv_one, mul_one]
  push_cast
  norm_num

/-! ## §4. Numerical bounds for `exp` -/

theorem exp_neg_le_of {y c : ℝ} (hc : 0 < c) (h : c ≤ Real.exp y) : Real.exp (-y) ≤ 1 / c := by
  rw [Real.exp_neg, inv_eq_one_div]; exact one_div_le_one_div_of_le hc h

theorem exp_nat_ge (k : ℕ) : (2.718 : ℝ) ^ k ≤ Real.exp k := by
  have h1 := Real.exp_one_gt_d9
  have : Real.exp (k : ℝ) = Real.exp 1 ^ k := by rw [← Real.exp_nat_mul]; ring_nf
  rw [this]
  exact pow_le_pow_left₀ (by norm_num) (by linarith) k

theorem exp_quad_ge {y : ℝ} (hy : 0 ≤ y) : 1 + y + y ^ 2 / 2 ≤ Real.exp y :=
  Real.quadratic_le_exp_of_nonneg hy

theorem pi_gt' : (3.14 : ℝ) < π := Real.pi_gt_d2
theorem pi_lt' : π < (3.15 : ℝ) := Real.pi_lt_d2

/-- `e^{−π} ≤ 1/20`. -/
theorem exp_neg_pi_le : Real.exp (-π) ≤ 1 / 20 := by
  have h := exp_nat_ge 3
  have : Real.exp 3 ≤ Real.exp π := Real.exp_le_exp.mpr (by linarith [pi_gt'])
  refine exp_neg_le_of (by norm_num) ?_
  push_cast at h; nlinarith

/-- `e^{−π/4} ≤ 0.48`. -/
theorem exp_neg_pi_div_four_le : Real.exp (-(π / 4)) ≤ 0.48 := by
  have hp := pi_gt'
  have h := exp_quad_ge (y := π / 4) (by positivity)
  have : (0.48 : ℝ) = 1 / (1 / 0.48) := by norm_num
  rw [this]; refine exp_neg_le_of (by norm_num) ?_
  nlinarith

/-- `e^{−π/16} ≤ 0.83`. -/
theorem exp_neg_pi_div_sixteen_le : Real.exp (-(π / 16)) ≤ 0.83 := by
  have hp := pi_gt'
  have h := exp_quad_ge (y := π / 16) (by positivity)
  have : (0.83 : ℝ) = 1 / (1 / 0.83) := by norm_num
  rw [this]; refine exp_neg_le_of (by norm_num) ?_
  nlinarith

/-- `e^{−9π/16} ≤ 0.18`. -/
theorem exp_neg_nine_pi_div_sixteen_le : Real.exp (-(9 * π / 16)) ≤ 0.18 := by
  have hp := pi_gt'
  have h1 := exp_nat_ge 1
  have h := exp_quad_ge (y := 9 * π / 16 - 1) (by linarith)
  have hsplit : Real.exp (9 * π / 16) = Real.exp 1 * Real.exp (9 * π / 16 - 1) := by
    rw [← Real.exp_add]; ring_nf
  have : (0.18 : ℝ) = 1 / (1 / 0.18) := by norm_num
  rw [this]; refine exp_neg_le_of (by norm_num) ?_
  rw [hsplit]
  push_cast at h1
  have hu : (0.766 : ℝ) ≤ 9 * π / 16 - 1 := by linarith
  have h2 : (2.059 : ℝ) ≤ Real.exp (9 * π / 16 - 1) := by nlinarith
  nlinarith

/-- `e^{−3π/2} ≤ 1/50`. -/
theorem exp_neg_three_pi_div_two_le : Real.exp (-(3 * π / 2)) ≤ 1 / 50 := by
  have h := exp_nat_ge 4
  have : Real.exp 4 ≤ Real.exp (3 * π / 2) := Real.exp_le_exp.mpr (by linarith [pi_gt'])
  refine exp_neg_le_of (by norm_num) ?_
  push_cast at h; nlinarith

/-- `e^{−5π/2} ≤ 1/1000`. -/
theorem exp_neg_five_pi_div_two_le : Real.exp (-(5 * π / 2)) ≤ 1 / 1000 := by
  have h := exp_nat_ge 7
  have : Real.exp 7 ≤ Real.exp (5 * π / 2) := Real.exp_le_exp.mpr (by linarith [pi_gt'])
  refine exp_neg_le_of (by norm_num) ?_
  push_cast at h; nlinarith

end ZInQ.Contrib.TYZLcal
