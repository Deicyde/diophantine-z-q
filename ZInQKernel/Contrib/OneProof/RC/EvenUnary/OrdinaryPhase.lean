import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Relative
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.OddDenominator
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.PrimeGauss
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Compute the residual phase of the ordinary theta ratio using the
lower-right entry as odd denominator. -/

noncomputable section
set_option maxHeartbeats 1000000

namespace ZInQ.Manuscript.RC.EvenUnary

open Complex CongruenceSubgroup HalfIntegral Matrix Matrix.SpecialLinearGroup PrintsAnalytic
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

private theorem coe_action (γ : SL(2, ℤ)) (z : ℍ) :
    (↑(γ • z) : ℂ) =
      (((γ 0 0 : ℤ) : ℂ) * (z : ℂ) + (γ 0 1 : ℤ)) / denom γ z := by
  rw [coe_specialLinearGroup_apply, ModularGroup.denom_apply]
  simp

private theorem theta_inversion {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * jacobiTheta τ := by
  let z : ℍ := ⟨τ, hτ⟩
  have h := jacobiTheta_S_smul z
  rw [modular_S_smul] at h
  change jacobiTheta (-τ)⁻¹ = _ at h
  simpa only [neg_inv, one_div, neg_div] using h

private theorem sqrt_mul_positive (x : ℂ) (r : ℝ) (hr : 0 < r) (hx : x ≠ 0) :
    ((r : ℂ) * x) ^ (1 / 2 : ℂ) =
      (r : ℂ) ^ (1 / 2 : ℂ) * x ^ (1 / 2 : ℂ) := by
  have hrc : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hrc hx), log_ofReal_mul hr hx,
    cpow_def_of_ne_zero hx, cpow_def_of_ne_zero hrc, ofReal_log hr.le, add_mul, exp_add]

private theorem ratio_odd_denom {j p : ℕ} [NeZero p] (hj : 0 < j) (hp : Odd p)
    (γ : SL(2, ℤ)) (hd : γ 1 1 = (p : ℤ))
    (hγ : ((4 * j : ℕ) : ℤ) ∣ γ 1 0) (z : ℍ) :
    dilatedThetaRatio j γ z =
      (((-I * (2 * (z : ℂ))) ^ (1 / 2 : ℂ)) /
        ((-I * (2 * (p : ℂ) * (z : ℂ) / denom γ z)) ^ (1 / 2 : ℂ))) *
        quadraticFourier (((j : ℤ) * γ 0 1 : ℤ) : ZMod p) 0 := by
  let a := γ 0 0
  let b := γ 0 1
  let c := γ 1 0
  let D := denom γ z
  let b' : ℤ := j * b
  let α : ℂ := 2 * (j : ℂ) * (z : ℂ)
  let β : ℂ := (p : ℂ) * α / D
  have hD : D ≠ 0 := denom_ne_zero γ z
  have hjC : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hα : 0 < α.im := by
    dsimp [α]
    rw [show (2 * (j : ℂ)) = (((2 * (j : ℝ) : ℝ)) : ℂ) by simp, im_ofReal_mul]
    exact mul_pos (by positivity) z.im_pos
  have hαN : α ≠ 0 := fun h => by simp [h] at hα
  obtain ⟨q, hq⟩ := hγ
  let e := 4 * q
  have he : c = j * e := by rw [show c = γ 1 0 from rfl, hq]; push_cast [e]; ring
  have hD' : D = (c : ℂ) * z + (p : ℂ) := by
    rw [show D = denom γ z from rfl, ModularGroup.denom_apply, hd, Int.cast_natCast]
  have hdet : a * p - b * c = 1 := by
    have h := γ.det_coe
    rwa [det_fin_two, hd] at h
  have hde : (b' : ZMod p) * (e : ZMod p) = -1 := by
    have hb : a * (p : ℤ) - b' * e = 1 := by
      rw [he] at hdet
      dsimp [b']
      linear_combination hdet
    have hc := congrArg (Int.cast : ℤ → ZMod p) hb
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      mul_zero, zero_sub, Int.cast_one] at hc
    linear_combination -hc
  have harg : 2 * (j : ℂ) * (↑(γ • z) : ℂ) =
      2 * (b' : ℂ) / p + β / (p : ℂ)^2 := by
    have htr := congrArg (Int.cast : ℤ → ℂ) hdet
    push_cast at htr
    rw [coe_action, ← show D = denom γ z from rfl]
    dsimp only [β, α, b']
    push_cast
    field_simp [hD, hpC]
    rw [hD']
    linear_combination (z : ℂ) * htr
  have hβ : 0 < β.im := by
    have hi : 0 < ((j : ℂ) * (↑(γ • z) : ℂ)).im := by
      rw [← ofReal_natCast, im_ofReal_mul]
      exact mul_pos (by positivity) (γ • z : ℍ).im_pos
    have hs : 0 < (2 * ((j : ℂ) * (↑(γ • z) : ℂ))).im := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, im_ofReal_mul]
      positivity
    rw [← mul_assoc, harg] at hs
    rw [show (2 * (b' : ℂ) / p) = (((2 * (b' : ℝ) / p) : ℝ) : ℂ) by push_cast; rfl,
      add_im, ofReal_im, zero_add, show (p : ℂ)^2 = (((p : ℝ)^2 : ℝ) : ℂ) by push_cast; rfl,
      div_ofReal_im] at hs
    by_contra! hh
    exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg hh (sq_nonneg (p : ℝ)))) hs
  have hInv : -1 / β = -1 / α - (e : ℂ) / (2 * p) := by
    dsimp only [β]
    field_simp [hD, hpC, hαN]
    rw [hD', he]
    dsimp only [α]
    push_cast
    ring
  rw [dilatedThetaRatio, harg, ordinaryTheta_odd_denominator hp b' e hde ⟨q, rfl⟩ hβ hInv,
    theta_inversion hα]
  have hθ : jacobiTheta α ≠ 0 := jacobiTheta_ne_zero_of_im_pos hα
  change _ = _
  rw [← mul_assoc, mul_div_cancel_right₀ _ hθ]
  let x : ℂ := -I * (2 * (z : ℂ))
  let y : ℂ := -I * (2 * (p : ℂ) * (z : ℂ) / D)
  have hx : x ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (mul_ne_zero two_ne_zero z.ne_zero)
  have hy : y ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
      (div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpC) z.ne_zero) hD)
  have ha : -I * α = (j : ℂ) * x := by dsimp [α, x]; ring
  have hb : -I * β = (j : ℂ) * y := by dsimp [β, α, y]; ring
  change _ = x ^ (1 / 2 : ℂ) / y ^ (1 / 2 : ℂ) * quadraticFourier (b' : ZMod p) 0
  rw [ha, hb, ← ofReal_natCast j, sqrt_mul_positive _ _ (Nat.cast_pos.mpr hj) hx,
    sqrt_mul_positive _ _ (Nat.cast_pos.mpr hj) hy]
  have hjr : (((j : ℝ) : ℂ) ^ (1 / 2 : ℂ)) ≠ 0 :=
    cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) |>.2 (ofReal_ne_zero.mpr (by positivity))
  have hy' : y ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num) |>.2 hy
  field_simp [hjr, hy']


/-- The exact scalar for a matrix whose lower-right entry is a positive
odd prime. The analytic factor cancels between the two dilations. -/
theorem ordinaryPhase_prime {p j : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hj : 0 < j) (γ : SL(2, ℤ)) (hd : γ 1 1 = (p : ℤ))
    (hlev : ((4 * j : ℕ) : ℤ) ∣ γ 1 0) (z : ℍ) :
    denom γ z * dilatedThetaRatio j γ z =
      (jacobiSym (-(j : ℤ)) p : ℂ) * thetaMultiplier γ z ^ 3 := by
  let b := γ 0 1
  let D := denom γ z
  let zc : ℂ := z
  let R := (-I * (2 * zc)) ^ (1 / 2 : ℂ) / (-I * (2 * (p : ℂ) * zc / D)) ^ (1 / 2 : ℂ)
  have hR : R ^ 2 = D / (p : ℂ) := by
    dsimp only [R]
    rw [div_pow, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
      show (1 / 2 : ℂ) * (2 : ℕ) = 1 by norm_num, cpow_one, cpow_one]
    have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
    have hzc : zc ≠ 0 := z.ne_zero
    have hD : D ≠ 0 := denom_ne_zero γ z
    field_simp [hD, hpC, I_ne_zero, hzc]
  have hpo : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hJj : dilatedThetaRatio j γ z = R * quadraticFourier (((j : ℤ) * b : ℤ) : ZMod p) 0 :=
    ratio_odd_denom hj hpo γ hd hlev z
  have hfour : ((4 * 1 : ℕ) : ℤ) ∣ γ 1 0 := by
    apply dvd_trans _ hlev
    exact_mod_cast (show 4 * 1 ∣ 4*j by simp)
  have hJ : thetaMultiplier γ z = R * quadraticFourier (b : ZMod p) 0 := by
    simpa [dilatedThetaRatio, thetaMultiplier, thetaFun, b, R, D, zc, mul_assoc] using
      ratio_odd_denom (by decide : 0 < (1 : ℕ)) hpo γ hd hfour z
  obtain ⟨k, hk⟩ := hlev
  have hdet : (γ 0 0) * p - b * ((4 * (j : ℤ)) * k) = 1 := by
    have h := γ.det_coe
    rw [det_fin_two, hd, hk, Nat.cast_mul, Nat.cast_ofNat] at h
    exact h
  have hf : (b : ZMod p) * ((j : ℤ) : ZMod p) * (4 * (k : ZMod p)) = -1 := by
    have h := congrArg (Int.cast : ℤ → ZMod p) hdet
    push_cast at h
    simp only [ZMod.natCast_self, mul_zero, zero_sub] at h
    rw [Int.cast_natCast]
    linear_combination -h
  have hb : IsUnit (b : ZMod p) :=
    (Units.mkOfMulEqOne _ (-(j : ZMod p) * (4 * (k : ZMod p)))
      (by push_cast at hf; linear_combination -hf)).isUnit
  have hj' : IsUnit (((j : ℤ)) : ZMod p) :=
    (Units.mkOfMulEqOne _ (-(b : ZMod p) * (4 * (k : ZMod p)))
      (by linear_combination -hf)).isUnit
  have hs : thetaMultiplier γ z ^ 2 = (jacobiSym (-1) p : ℂ) * D := by
    rw [hJ, mul_pow, hR, primeGauss_sq_jacobi hp hb]
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne p)]
  have hneg : (jacobiSym (-1) p : ℂ) ^ 2 = 1 := by
    exact_mod_cast (jacobiSym.sq_one (by simp [Int.gcd] : Int.gcd (-1) (p : ℤ) = 1))
  have hr : dilatedThetaRatio j γ z = (jacobiSym (j : ℤ) p : ℂ) * thetaMultiplier γ z := by
    rw [hJj, primeGauss_scale_jacobi hp hb hj', hJ]
    ring
  change D * dilatedThetaRatio j γ z = _
  rw [hr, show (-(j : ℤ)) = (-1) * (j : ℤ) by ring, jacobiSym.mul_left, Int.cast_mul,
    pow_succ, hs]
  linear_combination -((jacobiSym (j : ℤ) p : ℂ) * D * thetaMultiplier γ z) * hneg

end ZInQ.Manuscript.RC.EvenUnary
