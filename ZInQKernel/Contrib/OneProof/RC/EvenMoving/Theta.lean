import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Matrices
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Character
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.PrimeGauss
import ZInQKernel.Contrib.OneProof.RC.AppE.Galois
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! The theta multiplier comparison at tex 9507–9512. We compare Jacobi
theta values by Poisson resummation at a common rational denominator.
No formula for the absolute phase of a quadratic Gauss sum is assumed. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenMoving

open PrintsAnalytic HalfIntegral Complex Matrix.SpecialLinearGroup ModularGroup
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups Real

private theorem theta_double_im (z : ℍ) : 0 < (2 * (z : ℂ)).im := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul]
  exact mul_pos (by norm_num) z.im_pos

private theorem theta_nonzero (z : ℍ) : thetaFun z ≠ 0 :=
  jacobiTheta_ne_zero_of_im_pos (theta_double_im z)

private theorem theta_periodic (z : ℍ) (r : ℤ) : thetaFun (T ^ r • z) = thetaFun z := by
  have hper : Function.Periodic (fun w : ℂ ↦ jacobiTheta (2 * w)) 1 := by
    intro w
    change jacobiTheta (2 * (w + 1)) = jacobiTheta (2 * w)
    rw [show (2 : ℂ) * (w + 1) = 2 + 2*w by ring, jacobiTheta_two_add]
  rw [modular_T_zpow_smul, thetaFun, thetaFun, coe_vadd]
  simpa [add_comm] using hper.int_mul r (z : ℂ)

theorem thetaMultiplier_rightT (γ : SL(2, ℤ)) (r : ℤ) (z : ℍ) :
    thetaMultiplier (γ * T ^ r) z = thetaMultiplier γ (T ^ r • z) := by
  rw [thetaMultiplier, thetaMultiplier, mul_smul, theta_periodic]

theorem thetaMultiplier_leftT (γ : SL(2, ℤ)) (r : ℤ) (z : ℍ) :
    thetaMultiplier (T ^ r * γ) z = thetaMultiplier γ z := by
  rw [thetaMultiplier, thetaMultiplier, mul_smul, theta_periodic]

theorem thetaMultiplier_triangular {γ : SL(2, ℤ)} (hc : γ 1 0 = 0) (z : ℍ) :
    thetaMultiplier γ z = 1 := by
  have hdet : γ 0 0 * γ 1 1 = 1 := by simpa [hc] using det_eq γ
  have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 :=
    Int.isUnit_iff.mp (show IsUnit (γ 1 1) from
      (Units.mkOfMulEqOne _ _ (by simpa only [mul_comm] using hdet)).isUnit)
  have he : γ • z = T ^ (γ 0 1 * γ 1 1) • z := by
    apply UpperHalfPlane.ext
    rw [modular_T_zpow_smul, coe_vadd, sl_coord]
    rcases hd with h | h
    · have ha : γ 0 0 = 1 := by simpa [h] using hdet
      simp [h, ha, hc, add_comm]
    · have ha : γ 0 0 = -1 := by rw [h] at hdet; omega
      simp [h, ha, hc]
      ring
  rw [thetaMultiplier, he, theta_periodic, div_self (theta_nonzero z)]

private def rightTau (γ : SL(2, ℤ)) (z : ℍ) : ℂ :=
  2 * (γ 1 1 : ℤ) * (z : ℂ) / ((γ 1 0 : ℤ) * (z : ℂ) + (γ 1 1 : ℤ))

private theorem theta_prime_formula {q : ℕ} [Fact q.Prime] (hq : q ≠ 2)
    (γ : SL(2, ℤ)) (hd : γ 1 1 = (q : ℤ)) (h4 : (4 : ℤ) ∣ γ 1 0) (z : ℍ) :
    thetaMultiplier γ z =
      ((-Complex.I * (2 * (z : ℂ))) ^ (1 / 2 : ℂ) / (-Complex.I * rightTau γ z) ^ (1 / 2 : ℂ)) *
        quadraticFourier ((γ 0 1 : ℤ) : ZMod q) 0 := by
  obtain ⟨k, hk⟩ := h4
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hz0 : (z : ℂ) ≠ 0 := fun h => z.im_ne_zero (by simpa only [coe_im, Complex.zero_im] using congrArg Complex.im h)
  have hd0 : ((γ 1 0 : ℤ) * (z : ℂ) + (γ 1 1 : ℤ)) ≠ 0 := by
    simpa only [ModularGroup.denom_apply] using denom_ne_zero (γ : GL (Fin 2) ℝ) z
  have ht : 2 * ((γ • z : ℍ) : ℂ) =
      2 * (γ 0 1 : ℤ) / q + rightTau γ z / (q : ℂ) ^ 2 := by
    have hh := congrArg (fun x : ℤ => (x : ℂ)) (det_eq γ)
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at hh
    rw [sl_coord, rightTau]
    simp only [hd, Int.cast_natCast] at hh hd0 ⊢
    have hd0' : (z : ℂ) * (γ 1 0 : ℤ) + (q : ℂ) ≠ 0 := by
      simpa only [mul_comm (z : ℂ)] using hd0
    field_simp [hq0, hd0, hd0']
    linear_combination (z : ℂ) * hh
  have htim : 0 < (rightTau γ z).im := by
    have hi := congrArg Complex.im ht
    have hs := theta_double_im (γ • z)
    have hqpos : 0 < (q : ℝ) := Nat.cast_pos.mpr (Fact.out : q.Prime).pos
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_intCast, ← Complex.ofReal_ofNat,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_div,
      Complex.add_im, Complex.ofReal_im, zero_add, Complex.div_ofReal_im] at hi
    exact (div_pos_iff_of_pos_right (pow_pos hqpos 2)).mp (hi ▸ hs)
  have hbc : (γ 0 1 : ZMod q) * (-(4 * (k : ZMod q))) = 1 := by
    have hh := congrArg (Int.castRingHom (ZMod q)) (det_eq γ)
    simp [hd, hk] at hh
    linear_combination hh
  have hinv : -1 / rightTau γ z = -1 / (2 * (z : ℂ)) - 2 * (k : ℂ) / q := by
    unfold rightTau
    simp only [hd, Int.cast_natCast, hk, Int.cast_mul, Int.cast_ofNat] at hd0 ⊢
    field_simp
    ring
  let w : ℍ := ⟨2 * (z : ℂ), theta_double_im z⟩
  have hinversion :
      jacobiTheta (-1 / (2 * (z : ℂ))) =
        (-Complex.I * (2 * (z : ℂ))) ^ (1 / 2 : ℂ) * thetaFun z := by
    have he := jacobiTheta_S_smul w
    rw [modular_S_smul] at he
    simpa only [w, UpperHalfPlane.coe_mk, inv_neg, neg_div, one_div, thetaFun] using he
  rw [thetaMultiplier]
  change jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) / thetaFun z = _
  rw [ht, theta_right_cusp hq _ _ hbc htim hinv, hinversion]
  rw [← mul_assoc, mul_div_cancel_right₀ _ (theta_nonzero z)]
  ring

private theorem cpow_nat_mul {p : ℕ} (hp : 0 < p) {v : ℂ} (hv : v ≠ 0) :
    ((p : ℂ) * v) ^ (1 / 2 : ℂ) = (p : ℂ) ^ (1 / 2 : ℂ) * v ^ (1 / 2 : ℂ) := by
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hp' hv), cpow_def_of_ne_zero hp',
    cpow_def_of_ne_zero hv, ← ofReal_natCast, log_ofReal_mul (Nat.cast_pos.mpr hp) hv]
  rw [ofReal_log (Nat.cast_nonneg p), add_mul, exp_add]

private theorem theta_scale_prime {p q : ℕ} [Fact q.Prime] (hp : 0 < p) (hq2 : q ≠ 2)
    (hpq : p < q) (γ δ : SL(2, ℤ))
    (hb : δ 0 1 = (p : ℤ) * γ 0 1) (hc : (p : ℤ) * δ 1 0 = γ 1 0)
    (hd : γ 1 1 = (q : ℤ)) (hd' : δ 1 1 = (q : ℤ))
    (h4 : (4 : ℤ) ∣ γ 1 0) (h4' : (4 : ℤ) ∣ δ 1 0) (z : ℍ) :
    thetaMultiplier δ (scalePoint p hp z) =
      (legendreSym q (p : ℤ) : ℂ) * thetaMultiplier γ z := by
  have ht : rightTau δ (scalePoint p hp z) = (p : ℂ) * rightTau γ z := by
    unfold rightTau
    rw [scalePoint_coe, hd, hd', ← hc]
    push_cast
    ring
  have hv : (2 * (z : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (fun h =>
    z.im_ne_zero (by simpa only [coe_im, Complex.zero_im] using congrArg Complex.im h))
  have ht0 : rightTau γ z ≠ 0 := by
    unfold rightTau
    refine div_ne_zero (mul_ne_zero ?_ (fun h => z.im_ne_zero (by simpa only [coe_im, Complex.zero_im] using congrArg Complex.im h))) ?_
    · rw [hd, Int.cast_natCast]
      exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
    · simpa only [ModularGroup.denom_apply] using denom_ne_zero (γ : GL (Fin 2) ℝ) z
  have hb0 : ((γ 0 1 : ℤ) : ZMod q) ≠ 0 := by
    intro h
    have e := congrArg (Int.castRingHom (ZMod q)) (det_eq γ)
    simp [hd, h] at e
  have hp0 : (p : ZMod q) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hp hpq
  have hG := quadraticFourier_prime_scale hq2 hb0 hp0
  rw [theta_prime_formula hq2 δ hd' h4', theta_prime_formula hq2 γ hd h4,
    ht, scalePoint_coe, hb]
  push_cast
  rw [mul_comm (p : ZMod q), hG]
  rw [legendreSym, Int.cast_natCast]
  rw [show -Complex.I * (2 * ((p : ℂ) * (z : ℂ))) = p * (-Complex.I * (2 * (z : ℂ))) by ring,
    show -Complex.I * ((p : ℂ) * rightTau γ z) = p * (-Complex.I * rightTau γ z) by ring,
    cpow_nat_mul hp (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hv),
    cpow_nat_mul hp (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) ht0),
    mul_div_mul_left _ _ (by
      exact cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hp.ne')))]
  ring

/-- Exact dilation comparison for the quotient of actual theta functions.
The coefficient is the positive-prime character on the raised level. -/
theorem thetaMultiplier_scale {m p : ℕ} [Fact p.Prime] (h4m : 4 ∣ m) (hpm : p ∣ m)
    (hodd : Odd p) (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 m)
    (h4δ : (4 : ℤ) ∣ δ 1 0)
    (ha : δ 0 0 = γ 0 0) (hb : δ 0 1 = (p : ℤ) * γ 0 1)
    (hc : (p : ℤ) * δ 1 0 = γ 1 0) (hd : δ 1 1 = γ 1 1) (z : ℍ) :
    thetaMultiplier δ (scalePoint p (Fact.out : p.Prime).pos z) =
      primeCharacter h4m hpm ((γ 1 1 : ℤ) : ZMod m) * thetaMultiplier γ z := by
  have hp := (Fact.out : p.Prime)
  have hcm := (mem_level_iff γ).mp hγ
  have h4γ : (4 : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr h4m).trans hcm
  rcases eq_or_ne (γ 1 0) 0 with hc0 | hc0
  · have hδ0 : δ 1 0 = 0 := (mul_eq_zero.mp (hc.trans hc0)).resolve_left (by exact_mod_cast hp.ne_zero)
    rw [thetaMultiplier_triangular hδ0, thetaMultiplier_triangular hc0, mul_one]
    have hdet : γ 0 0 * γ 1 1 = 1 := by simpa [hc0] using det_eq γ
    have hu : IsUnit (γ 1 1) :=
      (Units.mkOfMulEqOne _ _ (by simpa only [mul_comm] using hdet)).isUnit
    rcases Int.isUnit_iff.mp hu with h | h
    · rw [h, Int.cast_one, map_one]
    · rw [h, Int.cast_neg, Int.cast_one, primeCharacter_neg_one h4m hpm hodd]
  have hcop : IsCoprime (γ 1 1) ((γ 1 0).natAbs : ℤ) := by
    rw [Int.natCast_natAbs, IsCoprime.abs_right_iff]
    exact ⟨γ 0 0, -(γ 0 1), by simpa [sub_eq_add_neg, mul_comm] using det_eq γ⟩
  obtain ⟨q, hqbig, hq, hcong⟩ :=
    Nat.forall_exists_prime_gt_and_zmodEq (max p 2) (by simpa using hc0) hcop
  have hpq := (le_max_left p 2).trans_lt hqbig
  have hq2 := (ne_of_gt ((le_max_right p 2).trans_lt hqbig))
  have : Fact q.Prime := ⟨hq⟩
  have hdiv : γ 1 0 ∣ (q : ℤ) - γ 1 1 :=
    Int.modEq_iff_dvd.mp (Int.modEq_natAbs.mp hcong.symm)
  obtain ⟨r, hr⟩ := hdiv
  let γ' := γ * T ^ r
  let δ' := δ * T ^ ((p : ℤ) * r)
  obtain ⟨ha1, hb1, hc1, hd1⟩ := rightT_entries γ r
  obtain ⟨ha2, hb2, hc2, hd2⟩ := rightT_entries δ ((p : ℤ) * r)
  have hq1 : γ' 1 1 = (q : ℤ) := hd1.trans (by linarith)
  have hq2' : δ' 1 1 = (q : ℤ) := hd2.trans (by
    rw [hd, ← mul_assoc, mul_comm (δ 1 0) (p : ℤ), hc]
    linarith)
  have hγ' : γ' ∈ Gamma0 m := (mem_level_iff γ').mpr (hc1.symm ▸ hcm)
  have hqn : q.Coprime m := by
    have h := AppE.isCoprime_d_of_mem_Gamma0 hγ'
    rw [hq1] at h
    exact h.natCoprime
  have hchar : (legendreSym q (p : ℤ) : ℂ) =
      primeCharacter h4m hpm ((γ 1 1 : ℤ) : ZMod m) := by
    rw [jacobiSym.legendreSym.to_jacobiSym,
      ← kronecker_of_odd _ (hq.odd_of_ne_two hq2), ← primeCharacter_nat h4m hpm hodd hqn]
    congr 1
    rw [← Int.cast_natCast, ← hq1, hd1, Int.cast_add, Int.cast_mul,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hcm, zero_mul, add_zero]
  let w := T ^ (-r) • z
  have hs : T ^ ((p : ℤ) * r) • scalePoint p hp.pos w =
      scalePoint p hp.pos (T ^ r • w) := by
    apply UpperHalfPlane.ext
    rw [modular_T_zpow_smul, coe_vadd, scalePoint_coe, scalePoint_coe, modular_T_zpow_smul, coe_vadd]
    push_cast
    ring
  have hstep := theta_scale_prime hp.pos hq2 hpq γ' δ' (by
    change (δ * T ^ ((p : ℤ) * r)) 0 1 = (p : ℤ) * (γ * T ^ r) 0 1
    rw [hb1, hb2, ha, hb]
    ring)
    (by simpa only [γ', δ', hc1, hc2] using hc) hq1 hq2'
    (hc1.symm ▸ h4γ) (hc2.symm ▸ h4δ) w
  have hw : T ^ r • w = z := by
    change T ^ r • (T ^ (-r) • z) = z
    rw [← mul_smul, ← zpow_add, add_neg_cancel, zpow_zero, one_smul]
  simpa only [γ', δ', thetaMultiplier_rightT, hs, hw, hchar] using hstep

end ZInQ.Manuscript.RC.EvenMoving
