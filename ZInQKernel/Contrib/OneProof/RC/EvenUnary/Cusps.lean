import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Resum
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.ThetaTransform

/-! The same weighted Poisson identity gives the cusp bound at arbitrary
denominators, whether or not they lie in the level (tex 9623). -/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Manuscript.RC.EvenUnary

open BlocksPerU Complex Matrix Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups Manifold

theorem weightedTheta_holo {B j : ℕ} [NeZero B] (v : ZMod B → ℂ) (hj : 0 < j) :
    MDiff (fun z : ℍ => weightedTheta v (2 * (j : ℂ) * (z : ℂ))) := by
  intro z
  have hi : 0 < (2 * (j : ℂ) * (z : ℂ)).im := by
    rw [show (2 * (j : ℂ)) = (((2 * (j : ℝ) : ℝ)) : ℂ) by simp, im_ofReal_mul]
    exact mul_pos (by positivity) z.im_pos
  exact (weightedTheta_differentiableAt v hi).mdifferentiableAt.comp z
    (mdifferentiableAt_const.mul z.mdifferentiable_coe)

private theorem coe_action (γ : SL(2, ℤ)) (z : ℍ) :
    (↑(γ • z) : ℂ) =
      (((γ 0 0 : ℤ) : ℂ) * (z : ℂ) + (γ 0 1 : ℤ)) /
        (((γ 1 0 : ℤ) : ℂ) * (z : ℂ) + (γ 1 1 : ℤ)) := by
  rw [coe_specialLinearGroup_apply]
  simp

private theorem im_neg_inv {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-1 / τ).im := by
  have hz : τ ≠ 0 := fun h => by simp [h] at hτ
  rw [neg_div, neg_im, one_div, inv_im, neg_div, neg_neg]
  exact div_pos hτ (normSq_pos.mpr hz)

private theorem neg_inv_neg_inv {w : ℂ} (hw : w ≠ 0) : -1 / (-1 / w) = w := by field_simp

private theorem norm_poisson_factor {C : ℕ} {A : ℝ} (hA : 0 < A) {D : ℂ} (hD : D ≠ 0) :
    ‖(C : ℂ) * ((1 / (-I * (-1 / (D / (A : ℂ)))) ^ (1 / 2 : ℂ)) /
      (-1 / (D / (A : ℂ))))‖ * ‖D‖ ^ (-(3 / 2) : ℝ) =
        (C : ℝ) * A ^ (-(3 / 2) : ℝ) := by
  let T := D / (A : ℂ)
  have hT : ‖T‖ = ‖D‖ / A := by
    rw [norm_div, norm_real, Real.norm_of_nonneg hA.le]
  have hn : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hTp : 0 < ‖T‖ := hT ▸ div_pos hn hA
  have hnorm : ‖-1 / T‖ = ‖T‖⁻¹ := by simp [one_div]
  have h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
  have hroot : ‖(-I * (-1 / T)) ^ (1 / 2 : ℂ)‖ = (‖T‖ ^ (1 / 2 : ℝ))⁻¹ := by
    rw [h, norm_cpow_real, norm_mul, norm_neg, norm_I, one_mul, hnorm,
      Real.inv_rpow (norm_nonneg _)]
  change ‖(C : ℂ) * ((1 / (-I * (-1 / T)) ^ (1 / 2 : ℂ)) / (-1 / T))‖ * _ = _
  rw [norm_mul, norm_div, norm_div, norm_one, hroot, hnorm,
    div_inv_eq_mul, div_inv_eq_mul, one_mul, Complex.norm_natCast]
  have hp : ‖T‖ ^ (1 / 2 : ℝ) * ‖T‖ = ‖T‖ ^ (3 / 2 : ℝ) := by
    conv_lhs => arg 2; rw [← Real.rpow_one ‖T‖]
    rw [← Real.rpow_add hTp]
    norm_num
  rw [hp, hT, Real.div_rpow hn.le hA.le, Real.rpow_neg hn.le, Real.rpow_neg hA.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hn (3/2))]

private theorem cusp_positive {B j : ℕ} [NeZero B] (v : ZMod B → ℂ) (hj : 0 < j)
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    IsBoundedAtImInfty (cuspNorm (3 / 2) (fun z => weightedTheta v (2 * (j : ℂ) * (z : ℂ))) γ) := by
  let c := (γ 1 0).toNat
  have hcc : (c : ℤ) = γ 1 0 := Int.toNat_of_nonneg hc.le
  have hc' : 0 < c := by omega
  let C := c * B
  have hC : 0 < C := Nat.mul_pos hc' (NeZero.pos B)
  letI : NeZero C := ⟨hC.ne'⟩
  let a : ℤ := j * γ 0 0 * B
  let A : ℝ := 2 * j * c * (B : ℝ)^2
  have hA : 0 < A := mul_pos
    (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hj)) (Nat.cast_pos.mpr hc'))
    (pow_pos (Nat.cast_pos.mpr (NeZero.pos B)) _)
  let w (z : ℍ) : ℂ := denom γ z / (A : ℂ)
  have hden (z : ℍ) : denom γ z = (c : ℂ) * (z : ℂ) + (γ 1 1 : ℤ) := by
    rw [ModularGroup.denom_apply, ← hcc, Int.cast_natCast]
  have hAim (z : ℍ) : (w z).im = ((c : ℝ) / A) * z.im := by
    dsimp only [w]
    rw [hden, div_ofReal_im, add_im, ← ofReal_natCast, im_ofReal_mul, intCast_im, add_zero]
    change (c : ℝ) * z.im / A = _
    ring
  have hw (z : ℍ) : 0 < (w z).im := by rw [hAim]; positivity
  have harg (z : ℍ) : 2 * (j : ℂ) * (↑(γ • z) : ℂ) =
      2 * (a : ℂ) / C + (-1 / w z) / (C : ℂ)^2 := by
    have hd := γ.det_coe
    rw [det_fin_two, ← hcc] at hd
    have hd' := congrArg (Int.cast : ℤ → ℂ) hd
    push_cast at hd'
    have hD := denom_ne_zero γ z
    rw [hden z] at hD
    have hcC : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc'.ne'
    have hBC : (B : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne B)
    dsimp only [w]
    rw [coe_action, hden, ← hcc]
    simp only [a, A, C, Int.cast_natCast, Int.cast_mul, ofReal_mul, ofReal_ofNat,
      ofReal_natCast, ofReal_pow, Nat.cast_mul]
    have hD' : (z : ℂ) * (c : ℂ) + (γ 1 1 : ℤ) ≠ 0 := by simpa only [mul_comm] using hD
    have hjC : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
    field_simp [hD, hD', hcC, hBC, hjC]
    linear_combination -hd'
  let V : ℝ := ∑' n : ℤ, |(n : ℝ)| * Real.exp (-π * (1 * (n : ℝ)^2))
  let S : ℝ := ∑ r : ZMod C, ‖v (ZMod.castHom (dvd_mul_left B c) (ZMod B) r) *
    ZMod.stdAddChar ((a : ZMod C) * r^2)‖ * V
  have hS (z : ℍ) (hz : A / (c : ℝ) ≤ z.im) :
      ‖∑ r : ZMod C, (v (ZMod.castHom (dvd_mul_left B c) (ZMod B) r) *
        ZMod.stdAddChar ((a : ZMod C) * r^2)) *
        linearTheta ((r.val : ℂ) / C) (w z)‖ ≤ S := by
    apply (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hy : 1 ≤ (w z).im := by
      rw [hAim, div_mul_eq_mul_div, le_div_iff₀ hA, one_mul]
      simpa only [mul_comm (c : ℝ)] using (div_le_iff₀ (Nat.cast_pos.mpr hc')).mp hz
    simpa only [V, ofReal_div, ofReal_natCast] using norm_linearTheta_le ((r.val : ℝ) / C) one_pos hy
  apply isBoundedAtImInfty_iff.mpr
  refine ⟨(C : ℝ) * A ^ (-(3 / 2) : ℝ) * S, A / (c : ℝ), fun z hz => ?_⟩
  have he := weightedTheta_rational_resum (dvd_mul_left B c) v a (im_neg_inv (hw z))
  rw [neg_inv_neg_inv (fun h => by simpa [h] using hw z)] at he
  rw [← harg z] at he
  rw [Real.norm_of_nonneg (by unfold cuspNorm; positivity), cuspNorm, he, norm_mul, mul_right_comm,
    norm_poisson_factor hA (denom_ne_zero γ z)]
  exact mul_le_mul_of_nonneg_left (hS z hz) (by positivity)


private theorem cusp_zero {B j : ℕ} [NeZero B] (v : ZMod B → ℂ) (hj : 0 < j)
    (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) :
    IsBoundedAtImInfty (cuspNorm (3 / 2) (fun z => weightedTheta v (2 * (j : ℂ) * (z : ℂ))) γ) := by
  let V : ℝ := ∑' n : ℤ, |(n : ℝ)| * Real.exp (-π * (1 * (n : ℝ)^2))
  let S : ℝ := ∑ r : ZMod B, ‖HalfIntegral.translationWeights v r‖ * V
  apply isBoundedAtImInfty_iff.mpr
  refine ⟨S, 1, fun z hz => ?_⟩
  have hdet := γ.det_coe
  rw [det_fin_two, hc, mul_zero, sub_zero] at hdet
  have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 :=
    Int.isUnit_iff.mp ((Units.mkOfMulEqOne _ _ (mul_comm _ _ |>.trans hdet)).isUnit)
  have hD : ‖denom γ z‖ = 1 := by
    rw [ModularGroup.denom_apply, hc, Int.cast_zero, zero_mul, zero_add]
    rcases hd with hd | hd <;> simp [hd]
  let w : ℂ := 2 * (j : ℂ) * (↑(γ • z) : ℂ)
  have hw : 1 ≤ w.im := by
    have he : ((↑(γ • z) : ℂ)).im = z.im := by
      rw [coe_action, hc, Int.cast_zero, zero_mul, zero_add]
      rcases hd with hd | hd
      · have ha : γ 0 0 = 1 := by simpa [hd] using hdet
        simp [hd, ha, add_im]
      · have ha : γ 0 0 = -1 := by rw [hd] at hdet; omega
        simp only [hd, ha, Int.cast_neg, Int.cast_one, neg_one_mul, div_neg, div_one, neg_add,
          neg_neg, add_im, neg_im, intCast_im, neg_zero, add_zero]
        rfl
    dsimp only [w]
    rw [show 2 * (j : ℂ) = (((2 * (j : ℝ) : ℝ)) : ℂ) by simp, im_ofReal_mul, he]
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    calc
      (1 : ℝ) ≤ (2 * j) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hz (by positivity)
  rw [Real.norm_of_nonneg (by unfold cuspNorm; positivity), cuspNorm, hD, Real.one_rpow, mul_one]
  change ‖weightedTheta v w‖ ≤ S
  rw [weightedTheta_fourier v (zero_lt_one.trans_le hw)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [V, ofReal_div, ofReal_natCast] using norm_linearTheta_le ((r.val : ℝ) / B) one_pos hw

/-- The weight-`3/2` normal is bounded at every cusp, including matrices
outside the intrinsic transformation group. -/
theorem weightedTheta_cusps {B j : ℕ} [NeZero B] (v : ZMod B → ℂ) (hj : 0 < j)
    (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (cuspNorm (3 / 2) (fun z => weightedTheta v (2 * (j : ℂ) * (z : ℂ))) γ) := by
  rcases lt_trichotomy (γ 1 0) 0 with h | h | h
  · have h' : 0 < (-γ) 1 0 := neg_pos.mpr h
    convert cusp_positive v hj (-γ) h' using 1
    funext z
    simp only [cuspNorm, ModularGroup.SL_neg_smul, ModularGroup.denom_apply]
    have he : ((↑((-γ) 1 0) : ℂ) * (z : ℂ) + ↑((-γ) 1 1)) =
        -((↑(γ 1 0) : ℂ) * (z : ℂ) + ↑(γ 1 1)) := by
      change ((↑(-(γ 1 0)) : ℂ) * (z : ℂ) + ↑(-(γ 1 1))) = _
      push_cast
      ring
    rw [he, norm_neg]
  · exact cusp_zero v hj γ h
  · exact cusp_positive v hj γ h

end ZInQ.Manuscript.RC.EvenUnary
