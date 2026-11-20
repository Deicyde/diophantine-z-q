import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Jacobi
import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Transform

/-! The two analytic facts for the ordinary Jacobi theta factor. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenExpansion

open BlocksPerU Complex CongruenceSubgroup Matrix Matrix.SpecialLinearGroup ModularForm
open OldStageLaw PrintsAnalytic
open UpperHalfPlane hiding I
open scoped BigOperators MatrixGroups

/-- Boundedness at every cusp follows from the ternary sum of three squares. -/
theorem ordinaryTheta_cusps (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (cuspNorm (1 / 2) thetaFun γ) := by
  have h := gridTheta_cusps (a := referenceForm) (fun _ => Nat.zero_lt_one) referenceWeight γ
  obtain ⟨M, A, hMA⟩ := isBoundedAtImInfty_iff.mp h
  refine isBoundedAtImInfty_iff.mpr ⟨max 1 M, A, fun z hz => ?_⟩
  have hv : cuspNorm (1 / 2) thetaFun γ z ^ 3 =
      cuspNorm (3 / 2) (fun z => gridTheta referenceWeight z) γ z := by
    simp only [cuspNorm, gridTheta_reference, thetaFun, norm_pow, mul_pow]
    rw [← Real.rpow_natCast (‖denom γ z‖ ^ (-(1 / 2) : ℝ)) 3, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have hpos : 0 ≤ cuspNorm (1 / 2) thetaFun γ z := by unfold cuspNorm; positivity
  have hc : cuspNorm (1 / 2) thetaFun γ z ^ 3 ≤ M := by
    have hb := hMA z hz
    rw [← hv, Real.norm_of_nonneg (pow_nonneg hpos _)] at hb
    exact hb
  rw [Real.norm_of_nonneg hpos]
  by_contra! hcontra
  have h1 : 1 ≤ cuspNorm (1 / 2) thetaFun γ z := (le_max_left _ _).trans hcontra.le
  have h2 : cuspNorm (1 / 2) thetaFun γ z ≤ cuspNorm (1 / 2) thetaFun γ z ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ h1 (by decide : 1 ≤ 3)
  exact (not_le_of_gt ((le_max_right _ _).trans_lt hcontra)) (h2.trans hc)

/-- Jacobi's fourth-power transformation on Gamma0(4), with the theta
multiplier defined as the quotient of the two actual theta values. -/
theorem ordinaryTheta_fourth (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    thetaMultiplier γ z ^ 4 = denom γ z ^ 2 := by
  have h := jacobiTheta_fourth_transform γ hγ z
  have hz : thetaFun z ≠ 0 := by
    apply HalfIntegral.jacobiTheta_ne_zero_of_im_pos
    rw [show (2 : ℂ) = (↑(2 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul]
    exact mul_pos (by norm_num : (0 : ℝ) < 2) z.im_pos
  rw [thetaMultiplier, div_pow, (div_eq_iff (pow_ne_zero _ hz)), ModularGroup.denom_apply]
  exact h

theorem ordinaryThetaLaw : OrdinaryThetaLaw := ⟨ordinaryTheta_fourth, ordinaryTheta_cusps⟩


end ZInQ.Manuscript.RC.EvenExpansion
