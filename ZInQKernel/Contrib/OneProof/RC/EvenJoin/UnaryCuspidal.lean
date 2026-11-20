import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Assembly

/-! The linear factor kills the zero frequency in weighted unary Poisson
summation, giving vanishing at every cusp of the actual shell (tex 9620–9623). -/

noncomputable section

set_option maxHeartbeats 1200000

namespace ZInQ.Manuscript.RC.EvenJoin

open BlocksPerU EvenUnary Complex Matrix Matrix.SpecialLinearGroup Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups Topology

private def gaussianBound : ℝ :=
  ∑' n : ℤ, |(n : ℝ)| * Real.exp (-π * (1 * (n : ℝ)^2))

private theorem linearTheta_norm_le_decay (u : ℝ) {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖linearTheta (u : ℂ) τ‖ ≤
    Real.exp (-π * (τ.im - 1)) * gaussianBound := by
  have hp := zero_lt_one.trans_le hτ
  refine (norm_linearTheta_le u hp le_rfl).trans ?_
  rw [gaussianBound, ← tsum_mul_left]
  have hs (t : ℝ) (ht : 0 < t) :
      Summable (fun n : ℤ => |(n : ℝ)| * Real.exp (-π * (t * (n : ℝ)^2))) := by
    simpa using summable_pow_mul_jacobiTheta₂_term_bound 0 ht 1
  refine (hs τ.im hp).tsum_le_tsum (fun n => ?_) ((hs 1 one_pos).mul_left _)
  by_cases hn : n = 0
  · simp [hn]
  rw [mul_left_comm (Real.exp (-π * (τ.im - 1))) |(n : ℝ)|, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  have hsq : (1 : ℝ) ≤ (n : ℝ)^2 := by
    have hi : (1 : ℤ) ≤ n^2 := by
      rcases (show n ≤ -1 ∨ 1 ≤ n by omega) with hn' | hn' <;> nlinarith
    exact_mod_cast hi
  have he := mul_nonneg (sub_nonneg.mpr hτ) (sub_nonneg.mpr hsq)
  nlinarith only [show 0 ≤ π * ((τ.im - 1) * ((n : ℝ)^2 - 1)) from
    mul_nonneg Real.pi_pos.le he]

private theorem linearTheta_tendsto_zero {S : Type*} {l : Filter S} {w : S → ℂ}
    (u : ℝ) (hw : Tendsto (fun z => (w z).im) l atTop) :
    Tendsto (fun z => linearTheta (u : ℂ) (w z)) l (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (g := fun z => Real.exp (-π * ((w z).im - 1)) *
      gaussianBound)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [hw.eventually_ge_atTop 1] with z hz
    exact linearTheta_norm_le_decay u hz
  · have ht : Tendsto (fun z => π * ((w z).im - 1)) l atTop :=
      (by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-1 : ℝ) hw :
        Tendsto (fun z => (w z).im - 1) l atTop).const_mul_atTop Real.pi_pos
    simpa only [zero_mul, neg_mul, Function.comp_apply] using
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ht)).mul_const
        gaussianBound

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

private theorem cusp_positive_zero {B j : ℕ} [NeZero B] (v : ZMod B → ℂ) (hj : 0 < j)
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    IsZeroAtImInfty (cuspNorm (3 / 2) (fun z => weightedTheta v (2 * (j : ℂ) * (z : ℂ))) γ) := by
  let c := (γ 1 0).toNat
  have hcc : (c : ℤ) = γ 1 0 := Int.toNat_of_nonneg hc.le
  have hc' : 0 < c := by omega
  let C := c * B
  have hC : 0 < C := Nat.mul_pos hc' (NeZero.pos B)
  let _ : NeZero C := ⟨hC.ne'⟩
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
  have ht : Tendsto (fun z : ℍ => (w z).im) atImInfty atTop := by
    simpa only [hAim, atImInfty] using (tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop).const_mul_atTop
      (div_pos (Nat.cast_pos.mpr hc') hA)
  have hsum : Tendsto (fun z : ℍ => ∑ r : ZMod C,
      (v (ZMod.castHom (dvd_mul_left B c) (ZMod B) r) *
        ZMod.stdAddChar ((a : ZMod C) * r^2)) * linearTheta ((r.val : ℂ) / C) (w z))
      atImInfty (nhds 0) := by
    rw [← show (∑ _ : ZMod C, (0 : ℂ)) = 0 by simp]
    exact tendsto_finsetSum (s := Finset.univ)
      (fun r _ => by
        simpa only [mul_zero, ofReal_div, ofReal_natCast] using
          (linearTheta_tendsto_zero ((r.val : ℝ) / C) ht).const_mul
            (v (ZMod.castHom (dvd_mul_left B c) (ZMod B) r) *
              ZMod.stdAddChar ((a : ZMod C) * r^2)))
  change Tendsto _ atImInfty (nhds 0)
  apply (show Tendsto (fun z : ℍ => (C : ℝ) * A ^ (-(3 / 2) : ℝ) *
      ‖∑ r : ZMod C, (v (ZMod.castHom (dvd_mul_left B c) (ZMod B) r) *
        ZMod.stdAddChar ((a : ZMod C) * r^2)) * linearTheta ((r.val : ℂ) / C) (w z)‖)
      atImInfty (nhds 0) by
    simpa only [norm_zero, mul_zero] using hsum.norm.const_mul ((C : ℝ) * A ^ (-(3 / 2) : ℝ))).congr
  intro z
  have he := weightedTheta_rational_resum (dvd_mul_left B c) v a (im_neg_inv (hw z))
  rw [neg_inv_neg_inv (fun h => by simpa [h] using hw z)] at he
  rw [← harg z] at he
  symm
  rw [cuspNorm, he, norm_mul, mul_right_comm,
    norm_poisson_factor (C := C) hA (denom_ne_zero γ z)]

private theorem cusp_denominator_zero {B j : ℕ} [NeZero B] (v : ZMod B → ℂ) (hj : 0 < j)
    (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) :
    IsZeroAtImInfty (cuspNorm (3 / 2) (fun z => weightedTheta v (2 * (j : ℂ) * (z : ℂ))) γ) := by
  have hdet := γ.det_coe
  rw [det_fin_two, hc, mul_zero, sub_zero] at hdet
  have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 :=
    Int.isUnit_iff.mp ((Units.mkOfMulEqOne _ _ (mul_comm _ _ |>.trans hdet)).isUnit)
  have hD (z : ℍ) : ‖denom γ z‖ = 1 := by
    rw [ModularGroup.denom_apply, hc, Int.cast_zero, zero_mul, zero_add]
    rcases hd with hd | hd <;> simp [hd]
  let w (z : ℍ) : ℂ := 2 * (j : ℂ) * (↑(γ • z) : ℂ)
  have hwim (z : ℍ) : (w z).im = (2 * (j : ℝ)) * z.im := by
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
  have ht : Tendsto (fun z : ℍ => (w z).im) atImInfty atTop := by
    simpa only [hwim, atImInfty] using (tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop).const_mul_atTop
      (show 0 < 2 * (j : ℝ) by positivity)
  have hsum : Tendsto (fun z : ℍ => ∑ r : ZMod B,
      HalfIntegral.translationWeights v r * linearTheta ((r.val : ℂ) / B) (w z))
      atImInfty (nhds 0) := by
    rw [← show (∑ _ : ZMod B, (0 : ℂ)) = 0 by simp]
    exact tendsto_finsetSum (s := Finset.univ)
      (fun r _ => by
        simpa only [mul_zero, ofReal_div, ofReal_natCast] using
          (linearTheta_tendsto_zero ((r.val : ℝ) / B) ht).const_mul
            (HalfIntegral.translationWeights v r))
  change Tendsto _ atImInfty (nhds 0)
  apply (show Tendsto (fun z : ℍ => ‖∑ r : ZMod B,
      HalfIntegral.translationWeights v r * linearTheta ((r.val : ℂ) / B) (w z)‖)
      atImInfty (nhds 0) by simpa only [norm_zero] using hsum.norm).congr
  intro z
  rw [cuspNorm, hD z, Real.one_rpow, mul_one]
  change _ = ‖weightedTheta v (w z)‖
  rw [weightedTheta_fourier v (by rw [hwim]; positivity)]

/-- The Poisson series has zero constant term also at the cusps outside
the transformation group. -/
theorem weightedTheta_zeroAtCusps {B j : ℕ} [NeZero B] (v : ZMod B → ℂ) (hj : 0 < j)
    (γ : SL(2, ℤ)) :
    IsZeroAtImInfty (cuspNorm (3 / 2) (fun z => weightedTheta v (2 * (j : ℂ) * (z : ℂ))) γ) := by
  rcases lt_trichotomy (γ 1 0) 0 with h | h | h
  · have h' : 0 < (-γ) 1 0 := neg_pos.mpr h
    convert cusp_positive_zero v hj (-γ) h' using 1
    funext z
    simp only [cuspNorm, ModularGroup.SL_neg_smul, ModularGroup.denom_apply]
    have he : ((↑((-γ) 1 0) : ℂ) * (z : ℂ) + ↑((-γ) 1 1)) =
        -((↑(γ 1 0) : ℂ) * (z : ℂ) + ↑(γ 1 1)) := by
      change ((↑(-(γ 1 0)) : ℂ) * (z : ℂ) + ↑(-(γ 1 1))) = _
      push_cast
      ring
    rw [he, norm_neg]
  · exact cusp_denominator_zero v hj γ h
  · exact cusp_positive_zero v hj γ h

end ZInQ.Manuscript.RC.EvenJoin
