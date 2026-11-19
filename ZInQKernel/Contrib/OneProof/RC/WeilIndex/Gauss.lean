import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Local
import ZInQKernel.Contrib.OneProof.RC.Intertwine2.Local
import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! Finite quadratic sums and their sign convention, tex 8746–8753.
The finite sum calculations are on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.WeilIndex

open Intertwine Intertwine2 Visibility AddChar
open scoped BigOperators Real

/-- The finite counterpart of the negative local character. -/
def negativeChar (n : ℕ) [NeZero n] : AddChar (ZMod n) ℂ :=
  (ZMod.stdAddChar (N := n)).mulShift (-1)

/-- The quadratic sum of conductor dividing (n), with negative sign. -/
def quadraticSum (n : ℕ) [NeZero n] (u : ZMod n) : ℂ :=
  ∑ x : ZMod n, negativeChar n (u * x ^ 2)

theorem localPhase_fraction (p : Place) (j n : ℕ) :
    localPhase p ((j : ℚ_[p.val]) / (p.val : ℚ_[p.val]) ^ n) =
      negativeChar (p.val ^ n) (j : ZMod (p.val ^ n)) := by
  let r : ℚ := (j : ℚ) / (p.val : ℚ) ^ n
  have hr : (r : ℚ_[p.val]) = (j : ℚ_[p.val]) / (p.val : ℚ_[p.val]) ^ n := by
    push_cast [r]
    rfl
  rw [← hr]
  have hd : algebraMap ℚ RationalFiniteAdeles (localFraction p (r : ℚ_[p.val]) - r) ∈ integralAdeles := by
    intro t
    rw [diagonal_apply, Rat.cast_sub]
    by_cases ht : t = p
    · subst t
      rw [← neg_sub]
      exact (PadicInt.subring p.val).neg_mem (localFraction_spec p (r : ℚ_[p.val]))
    · exact (PadicInt.subring t.val).sub_mem (localFraction_elsewhere ht _)
        (prime_fraction_integral_elsewhere ht j n)
  rw [localPhase, rationalPhase_congr ((rational_integral _).mp hd)]
  simp only [negativeChar, mulShift_apply, neg_mul, one_mul, rationalPhase, r]
  have hj : ((-(j : ℤ) : ℤ) : ZMod (p.val ^ n)) = -(j : ZMod (p.val ^ n)) := by simp
  rw [← hj, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

private def complexQuadratic (p : Place) : MulChar (ZMod p.val) ℂ :=
  (quadraticChar (ZMod p.val)).ringHomComp (Int.castRingHom ℂ)

private theorem shifted_negative_primitive (p : Place) (u : (ZMod p.val)ˣ) :
    ((negativeChar p.val).mulShift (u : ZMod p.val)).IsPrimitive := by
  intro a ha
  rw [negativeChar, mulShift_mulShift, mulShift_mulShift]
  exact ZMod.isPrimitive_stdAddChar _ (mul_ne_zero (neg_ne_zero.mpr one_ne_zero)
    (mul_ne_zero u.ne_zero ha))

/-- The unweighted quadratic sum is the Gauss sum against the Legendre
character. The trivial additive sum disappears because the shift is a unit. -/
theorem quadraticSum_eq_gaussSum (p : Place) (hp : p.val ≠ 2) (u : (ZMod p.val)ˣ) :
    quadraticSum p.val u = gaussSum (complexQuadratic p) ((negativeChar p.val).mulShift u) := by
  classical
  let ψ := (negativeChar p.val).mulShift (u : ZMod p.val)
  have hψ : ψ ≠ 1 := by
    simpa only [ψ, mulShift_one] using shifted_negative_primitive p u (a := 1) one_ne_zero
  have hp' : ringChar (ZMod p.val) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  change (∑ x : ZMod p.val, ψ (x ^ 2)) = _
  rw [← Finset.sum_fiberwise' Finset.univ (fun x : ZMod p.val => x ^ 2) ψ]
  have hc (a : ZMod p.val) :
      ((Finset.univ.filter (fun x : ZMod p.val => x ^ 2 = a)).card : ℂ) = complexQuadratic p a + 1 := by
    have hf : (Finset.univ.filter (fun x : ZMod p.val => x ^ 2 = a)) = {x | x ^ 2 = a}.toFinset := by
      ext x
      simp
    rw [hf]
    have h := quadraticChar_card_sqrts hp' a
    simpa only [complexQuadratic, MulChar.ringHomComp_apply, Int.coe_castRingHom, Int.cast_natCast,
      Int.cast_add, Int.cast_one] using congrArg (fun z : ℤ => (z : ℂ)) h
  simp only [Finset.sum_const, nsmul_eq_mul, hc, add_mul, one_mul, Finset.sum_add_distrib]
  rw [AddChar.sum_eq_zero_of_ne_one hψ, add_zero]
  rfl

/-- Normalized Gauss sum at an odd prime when the coefficient has odd
valuation. Its square determines the phase up to the classical Gauss sign. -/
def oddGauss (p : Place) (u : (ZMod p.val)ˣ) : ℂ :=
  quadraticSum p.val u / (Real.sqrt p.val : ℂ)

theorem oddGauss_sq (p : Place) (hp : p.val ≠ 2) (u : (ZMod p.val)ˣ) :
    oddGauss p u ^ 2 = (ZMod.χ₄ (p.val : ZMod 4) : ℂ) := by
  have hp' : ringChar (ZMod p.val) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hχ : complexQuadratic p ≠ 1 := (MulChar.ringHomComp_ne_one_iff Int.cast_injective).2
    (quadraticChar_ne_one hp')
  have hs : (Real.sqrt p.val : ℂ) ^ 2 = (p.val : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p.val)
  have hpn : (p.val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  rw [oddGauss, div_pow, quadraticSum_eq_gaussSum p hp,
    gaussSum_sq hχ ((quadraticChar_isQuadratic _).comp (Int.castRingHom ℂ))
      (shifted_negative_primitive p u), hs, ZMod.card, mul_div_cancel_right₀ _ hpn]
  simp only [complexQuadratic, MulChar.ringHomComp_apply, Int.coe_castRingHom]
  have he := congrArg (fun z : ℤ => (z : ℂ)) (legendreSym.at_neg_one (p := p.val) hp)
  simpa only [legendreSym, Int.cast_neg, Int.cast_one] using he

theorem oddGauss_twist (p : Place) (hp : p.val ≠ 2) (u : (ZMod p.val)ˣ) :
    oddGauss p u = complexQuadratic p u * oddGauss p 1 := by
  rw [oddGauss, oddGauss, quadraticSum_eq_gaussSum p hp, quadraticSum_eq_gaussSum p hp,
    gaussSum_mulShift_eq]
  have hχ := ((quadraticChar_isQuadratic (ZMod p.val)).comp (Int.castRingHom ℂ)).inv
  rw [show (complexQuadratic p)⁻¹ = complexQuadratic p from hχ, Units.val_one, mulShift_one, mul_div_assoc]

theorem quadraticSum_four (u : ZMod 4) :
    quadraticSum 4 u = 2 + 2 * negativeChar 4 u := by
  unfold quadraticSum
  have hs := Fin.sum_univ_four (fun x : Fin 4 => negativeChar 4 (u * (show ZMod 4 from x) ^ 2))
  change (∑ x : ZMod 4, negativeChar 4 (u * x ^ 2)) = _ at hs
  rw [hs]
  change negativeChar 4 (u * (0 : ZMod 4) ^ 2) + negativeChar 4 (u * (1 : ZMod 4) ^ 2) +
    negativeChar 4 (u * (2 : ZMod 4) ^ 2) + negativeChar 4 (u * (3 : ZMod 4) ^ 2) = _
  simp only [show (0 : ZMod 4) ^ 2 = 0 by decide, one_pow,
    show (2 : ZMod 4) ^ 2 = 0 by decide, show (3 : ZMod 4) ^ 2 = 1 by decide,
    mul_zero, mul_one, map_zero_eq_one]
  ring

private theorem stdChar_eight (u : ZMod 8) :
    ZMod.stdAddChar u = (exponentRoot u : ℂ) := by
  have hu : ((u.val : ℤ) : ZMod 8) = u := by simp
  conv_lhs => rw [← hu, ZMod.stdAddChar_coe]
  simp only [exponentRoot, Units.val_pow_eq_pow_val, zetaEight, Units.val_mk0,
    ← Complex.exp_nat_mul]
  push_cast
  congr 1
  ring

set_option maxHeartbeats 1000000 in
theorem quadraticSum_eight (u : (ZMod 8)ˣ) :
    quadraticSum 8 u = 4 * (exponentRoot (-(u : ZMod 8)) : ℂ) := by
  have hu : (ZMod.cast (u : ZMod 8) : ZMod 2) ≠ 0 :=
    (u.isUnit.map (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2))).ne_zero
  have h4 : (u : ZMod 8) * 4 = 4 := by
    generalize (u : ZMod 8) = x at hu ⊢
    fin_cases x <;> first | decide | exact False.elim (hu (by decide))
  have hn4 : negativeChar 8 (4 : ZMod 8) = -1 := by
    simp only [negativeChar, mulShift_apply, show -(1 : ZMod 8) * 4 = 4 by decide, stdChar_eight]
    have hroot : exponentRoot (4 : ZMod 8) = -1 := zetaEight_pow_four
    rw [hroot, Units.val_neg, Units.val_one]
  unfold quadraticSum
  have hs := Fin.sum_univ_eight (fun x : Fin 8 => negativeChar 8 ((u : ZMod 8) * (show ZMod 8 from x) ^ 2))
  change (∑ x : ZMod 8, negativeChar 8 ((u : ZMod 8) * x ^ 2)) = _ at hs
  rw [hs]
  let f (x : ZMod 8) := negativeChar 8 ((u : ZMod 8) * x ^ 2)
  change f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 = _
  simp only [f, show (0 : ZMod 8) ^ 2 = 0 by decide, one_pow,
    show (2 : ZMod 8) ^ 2 = 4 by decide, show (3 : ZMod 8) ^ 2 = 1 by decide,
    show (4 : ZMod 8) ^ 2 = 0 by decide, show (5 : ZMod 8) ^ 2 = 1 by decide,
    show (6 : ZMod 8) ^ 2 = 4 by decide, show (7 : ZMod 8) ^ 2 = 1 by decide,
    mul_zero, mul_one, map_zero_eq_one, h4, hn4]
  have hphase : negativeChar 8 u = (exponentRoot (-(u : ZMod 8)) : ℂ) := by
    simp only [negativeChar, mulShift_apply, neg_mul, one_mul, stdChar_eight]
  rw [hphase]
  ring

private theorem negativeFour (j : ℤ) :
    negativeChar 4 (j : ZMod 4) = (exponentRoot ((-(2 * j) : ℤ) : ZMod 8) : ℂ) := by
  rw [← stdChar_eight]
  have hj : ((-j : ℤ) : ZMod 4) = -(1 : ZMod 4) * (j : ZMod 4) := by simp
  rw [negativeChar, mulShift_apply, ← hj, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

private theorem eighth_add_inv :
    (zetaEight : ℂ) + ((zetaEight⁻¹ : ℂˣ) : ℂ) = (Real.sqrt 2 : ℂ) := by
  have hc := congrArg (fun x : ℝ => (x : ℂ)) Real.cos_pi_div_four
  simp only [Complex.ofReal_cos, Complex.ofReal_div, Complex.ofReal_ofNat] at hc
  rw [Complex.cos] at hc
  rw [Units.val_inv_eq_inv_val]
  change Complex.exp (↑π / 4 * Complex.I) + (Complex.exp (↑π / 4 * Complex.I))⁻¹ = _
  rw [← Complex.exp_neg]
  rw [neg_mul] at hc
  linear_combination 2 * hc

private theorem eighth_normalized (g : ℂˣ)
    (h : (g : ℂ) + ((g⁻¹ : ℂˣ) : ℂ) = (Real.sqrt 2 : ℂ)) :
    (2 + 2 * (g : ℂ) ^ 2) / (2 * (Real.sqrt 2 : ℂ)) = (g : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hg := congrArg (fun z : ℂ => z * (g : ℂ)) h
  simp only [add_mul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ g.ne_zero] at hg
  apply (div_eq_iff (mul_ne_zero two_ne_zero hs)).2
  linear_combination 2 * hg

/-- At valuation parity zero the dyadic normalized sum is the
negative-character phase selected by the unit modulo four. -/
theorem dyadic_evenGauss (u : (ZMod 8)ˣ) :
    quadraticSum 4 (ZMod.cast (u : ZMod 8)) / (2 * (Real.sqrt 2 : ℂ)) =
      (exponentRoot (dyadicExponent false (u : ZMod 8)) : ℂ) := by
  have hunit : IsUnit (ZMod.cast (u : ZMod 8) : ZMod 4) :=
    u.isUnit.map (ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4))
  have hmod : (ZMod.cast (u : ZMod 8) : ZMod 4) = 1 ∨
      (ZMod.cast (u : ZMod 8) : ZMod 4) = 3 := by
    let x : ZMod 4 := ZMod.cast (u : ZMod 8)
    change x = 1 ∨ x = 3
    have hx : IsUnit x := hunit
    have hc : Nat.Coprime x.val 4 := by
      simpa only [hx.unit_spec] using ZMod.val_coe_unit_coprime hx.unit
    have hc2 := hc.of_dvd_right (by decide : 2 ∣ 4)
    have hn := Nat.prime_two.coprime_iff_not_dvd.mp hc2.symm
    have hl := ZMod.val_lt x
    have he : x.val = 1 ∨ x.val = 3 := by omega
    rw [← ZMod.natCast_zmod_val x]
    rcases he with h | h
    · exact Or.inl (by rw [h, Nat.cast_one])
    · exact Or.inr (by rw [h]; rfl)
  rcases hmod with h | h
  · rw [quadraticSum_four, h]
    rw [show negativeChar 4 1 = (((zetaEight⁻¹ : ℂˣ) : ℂ) ^ 2) by
      rw [← Int.cast_one, negativeFour, show ((-(2 * (1 : ℤ)) : ℤ) : ZMod 8) = -1 + -1 by decide,
        exponentRoot_add, exponentRoot_neg, exponentRoot_one, Units.val_mul, ← pow_two]]
    simp only [dyadicExponent, h, Bool.false_eq_true, ite_false, map_one, show (1 : ℤ) ≠ -1 by decide,
      exponentRoot_neg, exponentRoot_one]
    apply eighth_normalized
    rw [inv_inv, add_comm, eighth_add_inv]
  · rw [quadraticSum_four, h]
    rw [show negativeChar 4 3 = (zetaEight : ℂ) ^ 2 by
      rw [show (3 : ZMod 4) = ((3 : ℤ) : ZMod 4) by decide, negativeFour,
        show ((-(2 * (3 : ℤ)) : ℤ) : ZMod 8) = 1 + 1 by decide,
        exponentRoot_add, exponentRoot_one, Units.val_mul, ← pow_two]]
    simp only [dyadicExponent, h, Bool.false_eq_true, ite_false, show ZMod.χ₄ (3 : ZMod 4) = -1 by decide,
      ite_true, exponentRoot_one]
    exact eighth_normalized _ eighth_add_inv

/-- At valuation parity one the dyadic normalized sum is the
negative-character phase of the full unit modulo eight. -/
theorem dyadic_oddGauss (u : (ZMod 8)ˣ) :
    quadraticSum 8 u / 4 = (exponentRoot (dyadicExponent true (u : ZMod 8)) : ℂ) := by
  rw [quadraticSum_eight, mul_comm, mul_div_cancel_right₀ _ (by norm_num)]
  rfl

#print axioms negativeFour
#print axioms eighth_add_inv
#print axioms eighth_normalized
#print axioms dyadic_evenGauss
#print axioms dyadic_oddGauss
#print axioms localPhase_fraction
#print axioms shifted_negative_primitive
#print axioms quadraticSum_eq_gaussSum
#print axioms oddGauss_sq
#print axioms oddGauss_twist
#print axioms quadraticSum_four
#print axioms stdChar_eight
#print axioms quadraticSum_eight

end ZInQ.Manuscript.RC.WeilIndex
