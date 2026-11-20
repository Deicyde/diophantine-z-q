import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Transform
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Cusps
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.ThetaNonvanishing
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Waldspurger

/-! The unary transformation relative to the ordinary theta function
at the same dilation. This separates weighted Poisson summation from the
ordinary theta multiplier comparison (tex 9548–9555, 9623–9625). -/

noncomputable section
set_option maxHeartbeats 1200000

namespace ZInQ.Manuscript.RC.EvenUnary

open Complex CongruenceSubgroup Matrix Matrix.SpecialLinearGroup PrintsAnalytic HalfIntegral
open UpperHalfPlane hiding I
open scoped MatrixGroups Manifold Real

/-- The ordinary theta ratio at shell dilation `j`. -/
def dilatedThetaRatio (j : ℕ) (γ : SL(2, ℤ)) (z : ℍ) : ℂ :=
  jacobiTheta (2 * (j : ℂ) * (↑(γ • z) : ℂ)) / jacobiTheta (2 * (j : ℂ) * (z : ℂ))

private theorem coe_action (γ : SL(2, ℤ)) (z : ℍ) :
    (↑(γ • z) : ℂ) =
      (((γ 0 0 : ℤ) : ℂ) * (z : ℂ) + (γ 0 1 : ℤ)) /
        (((γ 1 0 : ℤ) : ℂ) * (z : ℂ) + (γ 1 1 : ℤ)) := by
  rw [coe_specialLinearGroup_apply]
  simp

private theorem im_positive_mul (j : ℕ) (hj : 0 < j) (z : ℍ) :
    0 < ((j : ℂ) * (z : ℂ)).im := by
  rw [← ofReal_natCast, im_ofReal_mul]
  exact mul_pos (by positivity) z.im_pos

private theorem relative_pos {B j : ℕ} [NeZero B] (v : DirichletCharacter ℂ B)
    (hv : v.Odd) (hj : 0 < j) (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hlev : ((4 * B^2 * j : ℕ) : ℤ) ∣ γ 1 0) (z : ℍ) :
    weightedTheta v (2 * (j : ℂ) * (↑(γ • z) : ℂ)) =
      v (γ 1 1 : ℤ) * denom γ z * dilatedThetaRatio j γ z *
        weightedTheta v (2 * (j : ℂ) * (z : ℂ)) := by
  obtain ⟨l, hl⟩ := hlev
  have hpos : 0 < l := pos_of_mul_pos_right (hl ▸ hc) (by positivity)
  lift l to ℕ using hpos.le
  let C := 4 * (B ^ 2 * l)
  have hlpos : 0 < l := by exact_mod_cast hpos
  have hBpos : 0 < B := Nat.pos_of_ne_zero (NeZero.ne B)
  have hC : 0 < C := by dsimp [C]; positivity
  let _ : NeZero (4 * (B ^ 2 * l)) := ⟨hC.ne'⟩
  have hBC : B ∣ 4 * (B ^ 2 * l) := ⟨4*B*l, by ring⟩
  have hc' : γ 1 0 = (C : ℤ) * (j : ℤ) := by rw [hl]; push_cast [C]; ring
  let a := γ 0 0
  let d := γ 1 1
  let b := γ 0 1
  let w : ℂ := j * (z : ℂ)
  have hw : 0 < w.im := im_positive_mul j hj z
  have ht : 0 < (2 * w).im := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, im_ofReal_mul]
    positivity
  have hden : denom γ z = (C : ℂ) * w + (d : ℂ) := by
    rw [ModularGroup.denom_apply, hc']
    push_cast [d, w]
    ring
  have hdet : a * d - b * ((C : ℤ) * (j : ℤ)) = 1 := by
    have h := γ.det_coe
    rw [det_fin_two, hc'] at h
    exact h
  have had : (a : ZMod C) * (d : ZMod C) = 1 := by
    simpa [Int.cast_mul, Int.cast_sub] using congrArg (Int.cast : ℤ → ZMod C) hdet
  have harg : 2 * (j : ℂ) * (↑(γ • z) : ℂ) =
      2 * (a : ℂ) / C - 2 / ((C : ℂ) * ((C : ℂ) * w + d)) := by
    have hd := denom_ne_zero γ z
    rw [hden] at hd
    have hcC : (C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hC.ne'
    have hdd := congrArg (Int.cast : ℤ → ℂ) hdet
    push_cast at hdd
    have hco : (↑(γ • z) : ℂ) = ((a : ℂ) * z + b) / denom γ z := by
      rw [coe_action, ModularGroup.denom_apply]
    rw [hco, hden]
    field_simp
    dsimp [w]
    linear_combination -hdd
  have hw2 : 2 * (j : ℂ) * (z : ℂ) = 2 * w := by simp only [w, mul_assoc]
  rw [harg, hw2, weightedTheta_at_cusp hBC v hv a d hw had, dilatedThetaRatio, harg, hw2,
    jacobiTheta_at_cusp (k := B ^ 2 * l) a d hw had, hden]
  rw [mul_div_cancel_right₀ _ (HalfIntegral.jacobiTheta_ne_zero_of_im_pos ht)]

private theorem relative_zero {B j : ℕ} (v : DirichletCharacter ℂ B) (hv : v.Odd)
    (hj : 0 < j) (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) (z : ℍ) :
    weightedTheta v (2 * (j : ℂ) * (↑(γ • z) : ℂ)) =
      v (γ 1 1 : ℤ) * denom γ z * dilatedThetaRatio j γ z *
        weightedTheta v (2 * (j : ℂ) * (z : ℂ)) := by
  let d := γ 1 1
  let b := γ 0 1
  have hdet := γ.det_coe
  rw [det_fin_two, hc, mul_zero, sub_zero] at hdet
  have hd : d = 1 ∨ d = -1 :=
    Int.isUnit_iff.mp ((Units.mkOfMulEqOne _ _ (mul_comm _ _ |>.trans hdet)).isUnit)
  have hγ : (↑(γ • z) : ℂ) = (z : ℂ) + ((b * d : ℤ) : ℂ) := by
    rw [coe_action, hc]
    rcases hd with hd | hd
    · have ha : γ 0 0 = 1 := by simpa [d, hd] using hdet
      have he : γ 1 1 = 1 := hd
      simp [he, hd, ha, b]
    · have he : γ 1 1 = -1 := hd
      have ha : γ 0 0 = -1 := by rw [he] at hdet; omega
      simp [he, ha, b, hd]
      ring
  have haction : 2 * (j : ℂ) * (↑(γ • z) : ℂ) =
      2 * (j : ℂ) * (z : ℂ) + (((j : ℤ) * b * d : ℤ) : ℂ) * 2 := by
    rw [hγ]; push_cast; ring
  have hθ : Function.Periodic jacobiTheta 2 := fun u => by rw [add_comm, jacobiTheta_two_add]
  rw [dilatedThetaRatio, haction, (weightedTheta_periodic v).int_mul _, hθ.int_mul _]
  have hpos : 0 < (2 * (j : ℂ) * (z : ℂ)).im := by
    rw [mul_assoc, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, im_ofReal_mul]
    exact mul_pos (by norm_num) (im_positive_mul j hj z)
  rw [div_self (HalfIntegral.jacobiTheta_ne_zero_of_im_pos hpos), mul_one, ModularGroup.denom_apply, hc]
  have hv' : v (-1) = -1 := hv
  change _ = v d * ((↑(0 : ℤ) : ℂ) * (z : ℂ) + (d : ℂ)) * _
  rcases hd with hd | hd <;> simp [hd, hv']

/-- At any level divisible by `4B²j`, the weighted law is the ordinary
dilated theta ratio times `v(d)(cz+d)`. It holds for the actual function
on the full group and does not require an evaluation of Gauss sums. -/
theorem weightedTheta_relative {B j : ℕ} [NeZero B] (v : DirichletCharacter ℂ B)
    (hv : v.Odd) (hj : 0 < j) (γ : SL(2, ℤ))
    (hlev : ((4 * B^2 * j : ℕ) : ℤ) ∣ γ 1 0) (z : ℍ) :
    weightedTheta v (2 * (j : ℂ) * (↑(γ • z) : ℂ)) =
      v (γ 1 1 : ℤ) * denom γ z * dilatedThetaRatio j γ z *
        weightedTheta v (2 * (j : ℂ) * (z : ℂ)) := by
  rcases lt_trichotomy (γ 1 0) 0 with h | h | h
  · have hc : 0 < (-γ) 1 0 := neg_pos.mpr h
    have hlev' : ((4 * B^2 * j : ℕ) : ℤ) ∣ (-γ) 1 0 := dvd_neg.mpr hlev
    have hh := relative_pos v hv hj (-γ) hc hlev' z
    have hv' : v (-1) = -1 := hv
    have hd : v (((-γ) 1 1 : ℤ) : ZMod B) = -v (γ 1 1 : ℤ) := by
      change v ((-(γ 1 1) : ℤ) : ZMod B) = _
      rw [Int.cast_neg, show (-(↑(γ 1 1) : ZMod B)) = -1 * ↑(γ 1 1) by ring, map_mul, hv']
      ring
    have hD : denom ((-γ : SL(2, ℤ)) : GL (Fin 2) ℝ) z = -denom γ z := by
      rw [ModularGroup.denom_apply (-γ) z, ModularGroup.denom_apply γ z]
      change (↑(-(γ 1 0)) : ℂ) * (z : ℂ) + ↑(-(γ 1 1)) = _
      push_cast
      ring
    have hcoeff : v (((-γ) 1 1 : ℤ) : ZMod B) * denom ((-γ : SL(2, ℤ)) : GL (Fin 2) ℝ) z =
        v (γ 1 1 : ℤ) * denom γ z :=
      (congrArg₂ (· * ·) hd hD).trans (neg_mul_neg _ _)
    have hprod := congrArg (fun y => y * dilatedThetaRatio j (-γ) z *
        weightedTheta v (2 * (j : ℂ) * (z : ℂ))) hcoeff
    have he := hh.trans hprod
    simpa only [dilatedThetaRatio, ModularGroup.SL_neg_smul] using he
  · exact relative_zero v hv hj γ h z
  · exact relative_pos v hv hj γ h hlev z

end ZInQ.Manuscript.RC.EvenUnary
