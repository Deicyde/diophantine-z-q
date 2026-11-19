import ZInQKernel.Contrib.OneProof.RC.Intertwine2.Index
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Reciprocity
import Mathlib.NumberTheory.Padics.RingHoms

/-! Explicit finite Weil factors for the negative local character.
The displayed formulas are the standard local quadratic Gauss sum
computation (on-the-spot (c)); the scalar identities are separated from
their oscillatory integral interpretation at tex 8746–8753. -/

noncomputable section

namespace ZInQ.Manuscript.RC.WeilIndex

open Intertwine Intertwine2 Visibility

/-- The place over two. -/
abbrev dyadicPlace : Place := ⟨2, Nat.prime_two⟩

/-- An exponent modulo eight as a complex unit. -/
def exponentRoot (e : ZMod 8) : ℂˣ := zetaEight ^ e.val

private theorem eighth_pow : zetaEight ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 by decide, pow_mul, zetaEight_pow_four, neg_one_sq]

theorem exponentRoot_add (a b : ZMod 8) :
    exponentRoot (a + b) = exponentRoot a * exponentRoot b := by
  rw [exponentRoot, ZMod.val_add, ← pow_eq_pow_mod _ eighth_pow, pow_add]
  rfl

@[simp] theorem exponentRoot_zero : exponentRoot 0 = 1 := rfl

@[simp] theorem exponentRoot_one : exponentRoot 1 = zetaEight := by
  change zetaEight ^ 1 = zetaEight
  exact pow_one _

theorem exponentRoot_neg (a : ZMod 8) : exponentRoot (-a) = (exponentRoot a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← exponentRoot_add, neg_add_cancel, exponentRoot_zero]

/-- The valuation of a nonzero coefficient. -/
def valAt (p : Place) (a : ℚ_[p.val]ˣ) : ℤ := Padic.valuation (a : ℚ_[p.val])

private theorem place_cast_ne_zero (p : Place) : (p.val : ℚ_[p.val]) ≠ 0 :=
  Nat.cast_ne_zero.mpr p.property.ne_zero

private def unitField (p : Place) (a : ℚ_[p.val]ˣ) : ℚ_[p.val] :=
  (a : ℚ_[p.val]) * (p.val : ℚ_[p.val]) ^ (-valAt p a)

private theorem unitField_norm (p : Place) (a : ℚ_[p.val]ˣ) : ‖unitField p a‖ = 1 := by
  have hx : unitField p a ≠ 0 := mul_ne_zero a.ne_zero (zpow_ne_zero _ (place_cast_ne_zero p))
  have hv : Padic.valuation (unitField p a) = 0 := by
    unfold unitField
    rw [Padic.valuation_mul a.ne_zero (zpow_ne_zero _ (place_cast_ne_zero p)),
      Padic.valuation_zpow, Padic.valuation_p, mul_one]
    exact add_neg_cancel _
  rw [Padic.norm_eq_zpow_neg_valuation hx, hv, neg_zero, zpow_zero]

private def unitInteger (p : Place) (a : ℚ_[p.val]ˣ) : ℤ_[p.val] :=
  ⟨unitField p a, (unitField_norm p a).le⟩

private theorem unitInteger_isUnit (p : Place) (a : ℚ_[p.val]ˣ) :
    IsUnit (unitInteger p a) :=
  PadicInt.isUnit_iff.mpr (unitField_norm p a)

/-- Remove the full power of the uniformizer, leaving a unit of the
integer ring. -/
def unitAt (p : Place) (a : ℚ_[p.val]ˣ) : ℤ_[p.val]ˣ :=
  (unitInteger_isUnit p a).unit

theorem unitAt_coe (p : Place) (a : ℚ_[p.val]ˣ) :
    ((unitAt p a : ℤ_[p.val]) : ℚ_[p.val]) =
      (a : ℚ_[p.val]) * (p.val : ℚ_[p.val]) ^ (-valAt p a) :=
  congrArg (fun z : ℤ_[p.val] => (z : ℚ_[p.val])) (unitInteger_isUnit p a).unit_spec

theorem valAt_mul (p : Place) (a b : ℚ_[p.val]ˣ) :
    valAt p (a * b) = valAt p a + valAt p b :=
  Padic.valuation_mul a.ne_zero b.ne_zero

theorem unitAt_mul (p : Place) (a b : ℚ_[p.val]ˣ) :
    unitAt p (a * b) = unitAt p a * unitAt p b := by
  apply Units.ext
  apply Subtype.ext
  change ((unitAt p (a * b) : ℤ_[p.val]) : ℚ_[p.val]) =
    ((unitAt p a : ℤ_[p.val]) : ℚ_[p.val]) * ((unitAt p b : ℤ_[p.val]) : ℚ_[p.val])
  simp only [unitAt_coe, valAt_mul, neg_add, zpow_add₀ (place_cast_ne_zero p), Units.val_mul]
  ac_rfl

/-- The residue of the unit at the odd primes. -/
def oddUnitResidue (p : Place) (a : ℚ_[p.val]ˣ) : (ZMod p.val)ˣ :=
  Units.map PadicInt.toZMod.toMonoidHom (unitAt p a)

/-- The unit residue modulo eight at the dyadic place. -/
def dyadicUnitResidue (a : ℚ_[dyadicPlace.val]ˣ) : (ZMod 8)ˣ :=
  Units.map (PadicInt.toZModPow (p := 2) 3).toMonoidHom (unitAt dyadicPlace a)

theorem dyadicUnitResidue_mul (a b : ℚ_[dyadicPlace.val]ˣ) :
    dyadicUnitResidue (a * b) = dyadicUnitResidue a * dyadicUnitResidue b := by
  unfold dyadicUnitResidue
  rw [unitAt_mul, map_mul]

theorem oddUnitResidue_mul (p : Place) (a b : ℚ_[p.val]ˣ) :
    oddUnitResidue p (a * b) = oddUnitResidue p a * oddUnitResidue p b := by
  unfold oddUnitResidue
  rw [unitAt_mul, map_mul]

/-- The exponent at an odd prime: at even valuation the index is one;
at odd valuation it is the negative-character Gauss sign times the
Legendre symbol of the unit. -/
def oddExponent (p : Place) (a : ℚ_[p.val]ˣ) : ZMod 8 :=
  if valAt p a % 2 = 0 then 0 else
    oddBase (p.val : ZMod 4) +
      signExponent (quadraticChar (ZMod p.val) (oddUnitResidue p a : ZMod p.val))

/-- The finite eighth-root exponent. -/
def finiteExponent (p : Place) (a : ℚ_[p.val]ˣ) : ZMod 8 :=
  if h : p = dyadicPlace then by
    subst p
    exact dyadicExponent (decide (valAt dyadicPlace a % 2 ≠ 0)) (dyadicUnitResidue a : ZMod 8)
  else oddExponent p a

/-- The explicit finite-place family with the standard negative additive
character convention. -/
def finiteGamma : FiniteIndexFamily := fun p a => exponentRoot (finiteExponent p a)

theorem finiteExponent_dyadic (a : ℚ_[dyadicPlace.val]ˣ) :
    finiteExponent dyadicPlace a =
      dyadicExponent (decide (valAt dyadicPlace a % 2 ≠ 0)) (dyadicUnitResidue a : ZMod 8) := by
  simp [finiteExponent]

theorem finiteExponent_odd (p : Place) (h : p ≠ dyadicPlace) (a : ℚ_[p.val]ˣ) :
    finiteExponent p a = oddExponent p a := by
  simp [finiteExponent, h]

theorem finiteGamma_even_odd_place (p : Place) (h : p ≠ dyadicPlace) (a : ℚ_[p.val]ˣ)
    (ha : valAt p a % 2 = 0) : finiteGamma p a = 1 := by
  simp [finiteGamma, finiteExponent_odd p h, oddExponent, ha]

private theorem zmod8_unit_sq (x : ZMod 8) (h : IsUnit x) : x ^ 2 = 1 := by
  have hx : (ZMod.cast x : ZMod 2) ≠ 0 :=
    (h.map (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2))).ne_zero
  clear h
  fin_cases x <;> first | decide | exact False.elim (hx (by decide))

theorem finiteExponent_mul_sq (p : Place) (a b : ℚ_[p.val]ˣ) :
    finiteExponent p (a * b ^ 2) = finiteExponent p a := by
  have hv : valAt p (a * b ^ 2) % 2 = valAt p a % 2 := by
    simp only [pow_two, valAt_mul]; omega
  by_cases hp : p = dyadicPlace
  · subst p
    rw [finiteExponent_dyadic, finiteExponent_dyadic, hv]
    congr 1
    rw [pow_two, dyadicUnitResidue_mul, dyadicUnitResidue_mul, Units.val_mul, Units.val_mul]
    rw [← pow_two, zmod8_unit_sq _ ((dyadicUnitResidue b).isUnit), mul_one]
  · rw [finiteExponent_odd p hp, finiteExponent_odd p hp]
    simp only [oddExponent, hv]
    split
    · rfl
    · have hx : (oddUnitResidue p b : ZMod p.val) ≠ 0 := (oddUnitResidue p b).ne_zero
      rw [pow_two, oddUnitResidue_mul, oddUnitResidue_mul, Units.val_mul, Units.val_mul,
        ← pow_two, map_mul, quadraticChar_sq_one' hx, mul_one]

theorem finiteGamma_mul_sq (p : Place) (a b : ℚ_[p.val]ˣ) :
    finiteGamma p (a * b ^ 2) = finiteGamma p a := by
  rw [finiteGamma, finiteExponent_mul_sq]; rfl

/-- The valuation and unit of an integral coefficient presented as a
(p)-power times an integer prime to (p). -/
theorem unitAt_of_int_times_pow (p : Place) (a : ℚ_[p.val]ˣ) (b : ℤ) (k : ℕ)
    (hb : ¬ (p.val : ℤ) ∣ b)
    (ha : (a : ℚ_[p.val]) = (b : ℚ_[p.val]) * (p.val : ℚ_[p.val]) ^ k) :
    valAt p a = k ∧ (unitAt p a : ℤ_[p.val]) = (b : ℤ_[p.val]) := by
  have hb0 : b ≠ 0 := fun he => hb (he.symm ▸ dvd_zero _)
  have hv : valAt p a = k := by
    rw [valAt, ha, Padic.valuation_mul (Int.cast_ne_zero.mpr hb0)
      (pow_ne_zero _ (place_cast_ne_zero p)), Padic.valuation_intCast,
      padicValInt.eq_zero_of_not_dvd hb, Padic.valuation_pow, Padic.valuation_p]
    simp
  refine ⟨hv, ?_⟩
  apply Subtype.ext
  rw [unitAt_coe, hv, ha]
  push_cast
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (place_cast_ne_zero p), add_neg_cancel, zpow_zero,
    mul_one]

#print axioms unitAt_of_int_times_pow
#print axioms eighth_pow
#print axioms exponentRoot_add
#print axioms exponentRoot_zero
#print axioms exponentRoot_one
#print axioms exponentRoot_neg
#print axioms place_cast_ne_zero
#print axioms unitField_norm
#print axioms unitInteger_isUnit
#print axioms unitAt_coe
#print axioms valAt_mul
#print axioms unitAt_mul
#print axioms dyadicUnitResidue_mul
#print axioms oddUnitResidue_mul
#print axioms finiteExponent_dyadic
#print axioms finiteExponent_odd
#print axioms finiteGamma_even_odd_place
#print axioms zmod8_unit_sq
#print axioms finiteExponent_mul_sq
#print axioms finiteGamma_mul_sq

end ZInQ.Manuscript.RC.WeilIndex
