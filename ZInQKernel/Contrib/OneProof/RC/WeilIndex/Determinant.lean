import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Local

/-! The determinant correction contributed by the explicit finite factors
(tex 8694–8716 and 8891–8901). These residue calculations are on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.WeilIndex

open Intertwine Intertwine2 Visibility

/-- The four-index quotient of the quaternion norm form, expressed as an
exponent. Tex 8701–8712 identifies this quotient with the Hilbert symbol
for the genuine oscillatory indices. -/
def determinantExponent (p : Place) (u a : ℚ_[p.val]ˣ) : ZMod 8 :=
  finiteExponent p 1 + finiteExponent p (u * a) - finiteExponent p u - finiteExponent p a

theorem determinantExponent_value (p : Place) (u a : ℚ_[p.val]ˣ) :
    exponentRoot (determinantExponent p u a) =
      finiteGamma p 1 * finiteGamma p (u * a) / (finiteGamma p u * finiteGamma p a) := by
  simp only [determinantExponent, sub_eq_add_neg, exponentRoot_add, exponentRoot_neg, finiteGamma]
  rw [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

/-- For a unit (u) at an odd prime, the correction is one if the
valuation of (a) is even, and otherwise the Legendre symbol of (u). -/
theorem odd_unit_determinantExponent (p : Place) (hp : p ≠ dyadicPlace)
    (u a : ℚ_[p.val]ˣ) (hu : valAt p u = 0) :
    determinantExponent p u a = if valAt p a % 2 = 0 then 0 else
      signExponent (quadraticChar (ZMod p.val) (oddUnitResidue p u : ZMod p.val)) := by
  have h1 : valAt p 1 = 0 := by simp [valAt]
  have h0 : (0 : ℤ) % 2 = 0 := by decide
  by_cases ha : valAt p a % 2 = 0
  · simp only [determinantExponent, finiteExponent_odd p hp, oddExponent, h1, hu,
      valAt_mul, zero_add, h0, ha, ite_true, sub_self]
  · simp only [determinantExponent, finiteExponent_odd p hp, oddExponent, h1, hu,
      valAt_mul, zero_add, h0, ha, ite_true, ite_false, sub_zero]
    rw [oddUnitResidue_mul, Units.val_mul, map_mul, signExponent_mul
      (quadraticChar_dichotomy (oddUnitResidue p u).ne_zero)
      (quadraticChar_dichotomy (oddUnitResidue p a).ne_zero)]
    abel

private theorem zmod8_chi4_sign (x : ZMod 8) (hx : IsUnit x) :
    ZMod.χ₄ (ZMod.cast x) = 1 ∨ ZMod.χ₄ (ZMod.cast x) = -1 := by
  let y : (ZMod 4)ˣ := (hx.map (ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4))).unit
  have hy : (y : ZMod 4) = ZMod.cast x := (hx.map _).unit_spec
  have h : ZMod.χ₄ (ZMod.cast x) ≠ 0 := by
    rw [← hy, ← MulChar.coe_toUnitHom]
    exact (ZMod.χ₄.toUnitHom y).ne_zero
  exact (ZMod.isQuadratic_χ₄ _).resolve_left h

private theorem dyadic_unit_exponent_mul (u a : ZMod 8) (hu : IsUnit u) (ha : IsUnit a) :
    dyadicExponent false 1 + dyadicExponent false (u * a) -
      dyadicExponent false u - dyadicExponent false a =
        (if ZMod.χ₄ (ZMod.cast u) = -1 ∧ ZMod.χ₄ (ZMod.cast a) = -1 then 4 else 0) := by
  have h : ZMod.χ₄ (ZMod.cast (u * a)) = ZMod.χ₄ (ZMod.cast u) * ZMod.χ₄ (ZMod.cast a) := by
    change ZMod.χ₄ ((ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4)) (u * a)) = _
    rw [map_mul, map_mul]
    rfl
  simp only [dyadicExponent, Bool.false_eq_true, ite_false, h]
  have h1 : ZMod.χ₄ (ZMod.cast (1 : ZMod 8)) = 1 := by decide
  rw [h1]
  rcases zmod8_chi4_sign u hu with hu | hu <;> rcases zmod8_chi4_sign a ha with ha | ha <;>
    simp only [hu, ha] <;> decide

/-- For two dyadic units the four-index factor is minus one exactly when
both units are three modulo four. In particular for (m\equiv3\pmod4)
the correction as a character of (u) is `χ₄`. -/
theorem dyadic_unit_determinantExponent (u a : ℚ_[dyadicPlace.val]ˣ)
    (hu : valAt dyadicPlace u = 0) (ha : valAt dyadicPlace a = 0) :
    determinantExponent dyadicPlace u a =
      if ZMod.χ₄ (ZMod.cast (dyadicUnitResidue u : ZMod 8)) = -1 ∧
        ZMod.χ₄ (ZMod.cast (dyadicUnitResidue a : ZMod 8)) = -1 then 4 else 0 := by
  have h1 : valAt dyadicPlace 1 = 0 := by simp [valAt]
  have hr : (dyadicUnitResidue 1 : ZMod 8) = 1 := by
    obtain ⟨_, hi⟩ := unitAt_of_int_times_pow dyadicPlace 1 1 0 (by decide) (by norm_num)
    change PadicInt.toZModPow (p := 2) 3 (unitAt dyadicPlace 1 : ℤ_[2]) = _
    rw [hi, map_intCast, Int.cast_one]
  have hm : valAt dyadicPlace (u * a) = 0 := by
    rw [valAt_mul, hu, ha]
    decide
  unfold determinantExponent
  rw [finiteExponent_dyadic, finiteExponent_dyadic, finiteExponent_dyadic, finiteExponent_dyadic,
    h1, hm, hu, ha, hr, dyadicUnitResidue_mul, Units.val_mul]
  simp only [show decide ((0 : ℤ) % 2 ≠ 0) = false by decide]
  exact dyadic_unit_exponent_mul _ _ (dyadicUnitResidue u).isUnit (dyadicUnitResidue a).isUnit

#print axioms determinantExponent_value
#print axioms odd_unit_determinantExponent
#print axioms zmod8_chi4_sign
#print axioms dyadic_unit_exponent_mul
#print axioms dyadic_unit_determinantExponent

end ZInQ.Manuscript.RC.WeilIndex
