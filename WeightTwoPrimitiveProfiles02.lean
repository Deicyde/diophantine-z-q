import WeightTwoAxisClasses02

/-!
# Actual primitive-row weight-two profile convolution

The inverse-unit permutations are purely finite arithmetic. Their
inverse-square coefficients occur here only in the independently convergent
one-dimensional axis series. The profile relation is proved for every
primitive residue row, including rows with neither coordinate a unit.
No primitive two-dimensional weight-two Eisenstein modular form is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open Complex Filter Matrix ModularForm
open UpperHalfPlane hiding I
open scoped Topology Real ModularForm MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants

open ZInQ.Contrib.HeckePrimeRationality
open PrimitiveEisensteinNormalization PrimitiveEisensteinUnitSeries

/-- The actual two signed primitive axis delta profiles. -/
def axisProfile (N : ℕ) (p : Fin 2 → ZMod N) : ℂ :=
  (if p 0 = 0 ∧ p 1 = 1 then 1 else 0) +
    (if p 0 = 0 ∧ p 1 = -1 then 1 else 0)

lemma residue_val_dvd_iff (N : ℕ) [NeZero N] (v : ZMod N) :
    (N : ℤ) ∣ (v.val : ℤ) ↔ v = 0 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

lemma one_ne_zero_residue (N : ℕ) (hN : 3 ≤ N) : (1 : ZMod N) ≠ 0 := by
  intro h
  have hz : (N : ℤ) ∣ (1 : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd 1 N).mp (by simpa using h)
  have hn : N ∣ 1 := by exact_mod_cast hz
  have := Nat.le_of_dvd (by norm_num : 0 < (1 : ℕ)) hn
  omega

/-- Primitivity supplies good labels; it does not assert that either coordinate is a unit. -/
lemma primitive_residue_good (N : ℕ) (hN : 3 ≤ N) (p : PrimitiveRow N) :
    ¬ ((N : ℤ) ∣ ((p.1 0).val : ℤ) ∧ (N : ℤ) ∣ ((p.1 1).val : ℤ)) := by
  let : NeZero N := ⟨by omega⟩
  rintro ⟨h0, h1⟩
  have hp0 := (residue_val_dvd_iff N (p.1 0)).mp h0
  have hp1 := (residue_val_dvd_iff N (p.1 1)).mp h1
  obtain ⟨x, y, hxy⟩ := p.2
  simp only [hp0, hp1, mul_zero, zero_mul, add_zero] at hxy
  exact one_ne_zero_residue N hN hxy.symm

lemma inverse_unit_positive (N : ℕ) (u : (ZMod N)ˣ) (r s : ZMod N) :
    (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * r = 0 ∧
      ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * s = 1) ↔ r = 0 ∧ s = (u : ZMod N) := by
  constructor
  · rintro ⟨hr, hs⟩
    constructor
    · have h := congrArg (fun z : ZMod N => (u : ZMod N) * z) hr
      change u.val * (u.inv * r) = u.val * 0 at h
      simpa only [← mul_assoc, u.val_inv, one_mul, mul_zero] using h
    · have h := congrArg (fun z : ZMod N => (u : ZMod N) * z) hs
      change u.val * (u.inv * s) = u.val * 1 at h
      simpa only [← mul_assoc, u.val_inv, one_mul, mul_one] using h
  · rintro ⟨rfl, rfl⟩
    exact ⟨mul_zero _, u.inv_val⟩

lemma inverse_unit_negative (N : ℕ) (u : (ZMod N)ˣ) (r s : ZMod N) :
    (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * r = 0 ∧
      ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * s = -1) ↔ r = 0 ∧ s = -(u : ZMod N) := by
  constructor
  · rintro ⟨hr, hs⟩
    constructor
    · have h := congrArg (fun z : ZMod N => (u : ZMod N) * z) hr
      change u.val * (u.inv * r) = u.val * 0 at h
      simpa only [← mul_assoc, u.val_inv, one_mul, mul_zero] using h
    · have h := congrArg (fun z : ZMod N => (u : ZMod N) * z) hs
      change u.val * (u.inv * s) = u.val * (-1) at h
      simpa only [← mul_assoc, u.val_inv, one_mul, mul_neg, mul_one] using h
  · rintro ⟨rfl, rfl⟩
    constructor
    · exact mul_zero _
    · change u.inv * (-u.val) = -1
      rw [mul_neg, u.inv_val]

lemma axisProfile_inverse_unit (N : ℕ) (u : (ZMod N)ˣ) (p : Fin 2 → ZMod N) :
    axisProfile N (scaleResidue u⁻¹ p) =
      (if p 0 = 0 ∧ p 1 = (u : ZMod N) then 1 else 0) +
        (if p 0 = 0 ∧ p 1 = -(u : ZMod N) then 1 else 0) := by
  unfold axisProfile scaleResidue
  simp only [inverse_unit_positive N u, inverse_unit_negative N u]

/-- The primitive unit guard follows from the genuine common-divisor criterion, in both signs. -/
lemma primitive_axis_nonunit_impossible (N d : ℕ) (p : PrimitiveRow N)
    (hd : ¬ d.Coprime N) (h0 : p.1 0 = 0) :
    (d : ZMod N) ≠ p.1 1 ∧ -(d : ZMod N) ≠ p.1 1 := by
  constructor
  · intro h
    have hu : IsUnit (d : ZMod N) := p.2.isUnit_of_dvd'
      ⟨0, by simp [h0]⟩ ⟨1, by simpa only [mul_one] using h.symm⟩
    exact hd ((ZMod.isUnit_iff_coprime d N).mp hu)
  · intro h
    have hu : IsUnit (d : ZMod N) := p.2.isUnit_of_dvd'
      ⟨0, by simp [h0]⟩ ⟨-1, by simpa only [mul_neg, mul_one] using h.symm⟩
    exact hd ((ZMod.isUnit_iff_coprime d N).mp hu)

/-- Each unit-permutation coefficient is exactly one of the two signed one-dimensional terms. -/
theorem unit_axis_term (N : ℕ) [NeZero N] (p : PrimitiveRow N) (d : ℕ) :
    unitCoefficient N 2 d * axisProfile N (unitPermutation N d p).1 =
      if p.1 0 = 0 then signedAxisClass N ((p.1 1).val : ℤ) d else 0 := by
  classical
  by_cases hd : d.Coprime N
  · rw [unitCoefficient, ite_eq_left hd, unitPermutation, dite_eq_left hd]
    change ((d : ℂ) ^ 2)⁻¹ * axisProfile N
      (scaleResidue (ZMod.unitOfCoprime d hd)⁻¹ p.1) = _
    rw [axisProfile_inverse_unit]
    have hu : (ZMod.unitOfCoprime d hd : ZMod N) = (d : ZMod N) := rfl
    by_cases h0 : p.1 0 = 0
    · simp only [hu, h0, true_and, ite_true, signedAxisClass,
        Int.cast_natCast, ZMod.natCast_zmod_val]
      simp only [eq_comm]
    · simp only [hu, h0, false_and, ite_false, add_zero, mul_zero]
  · rw [unitCoefficient, ite_eq_right hd, zero_mul]
    by_cases h0 : p.1 0 = 0
    · obtain ⟨hpos, hneg⟩ := primitive_axis_nonunit_impossible N d p hd h0
      simp only [ite_eq_left h0, signedAxisClass, Int.cast_natCast, ZMod.natCast_zmod_val,
        ite_eq_right hpos, ite_eq_right hneg, add_zero, mul_zero]
    · simp only [ite_eq_right h0]

/-- Summability comes from the independently convergent signed axis series, not from a raw lattice series. -/
theorem unit_axis_summable (N : ℕ) (hN : 0 < N) (p : PrimitiveRow N) :
    Summable (fun d : ℕ => unitCoefficient N 2 d * axisProfile N (unitPermutation N d p).1) := by
  let : NeZero N := ⟨hN.ne'⟩
  by_cases h0 : p.1 0 = 0
  · exact (signedAxisClass_summable N hN ((p.1 1).val : ℤ)).congr
      (fun d => by simpa only [unit_axis_term N p d, ite_eq_left h0])
  · have he : (fun d : ℕ => unitCoefficient N 2 d * axisProfile N (unitPermutation N d p).1) =
        fun _ => (0 : ℂ) := funext (fun d => by simp only [unit_axis_term N p d, ite_eq_right h0])
    rw [he]
    exact summable_zero

/-- The actual weight-two constant on every primitive row satisfies the full unit convolution. -/
theorem primitive_xConstant_unit_series (N : ℕ) (hN : 3 ≤ N) (p : PrimitiveRow N) :
    xConstant N ((p.1 0).val : ℤ) ((p.1 1).val : ℤ) / (N : ℂ) ^ 2 +
      (Real.pi : ℂ) ^ 2 / (3 * (N : ℂ) ^ 2) =
      ∑' d : ℕ, unitCoefficient N 2 d * axisProfile N (unitPermutation N d p).1 := by
  let : NeZero N := ⟨by omega⟩
  have hNp : 0 < N := by omega
  have hg := primitive_residue_good N hN p
  by_cases h0 : p.1 0 = 0
  · have ha : (N : ℤ) ∣ ((p.1 0).val : ℤ) := (residue_val_dvd_iff N _).mpr h0
    have hb : ¬ (N : ℤ) ∣ ((p.1 1).val : ℤ) := fun h => hg ⟨ha, h⟩
    rw [xConstant_axis N _ _ ha hb]
    rw [normalized_axisConstant_eq_signed_sum N hNp _ hb]
    exact tsum_congr (fun d => by simpa only [unit_axis_term N p d, ite_eq_left h0])
  · have ha : ¬ (N : ℤ) ∣ ((p.1 0).val : ℤ) := fun h => h0 ((residue_val_dvd_iff N _).mp h)
    rw [xConstant_nonaxis N _ _ ha]
    have he : (fun d : ℕ => unitCoefficient N 2 d * axisProfile N (unitPermutation N d p).1) =
        fun _ => (0 : ℂ) := funext (fun d => by simp only [unit_axis_term N p d, ite_eq_right h0])
    rw [he, tsum_zero]
    have hn0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNp.ne'
    field_simp [hn0]
    ring

lemma unit_axis_zero (N : ℕ) (hN : 3 ≤ N) (p : PrimitiveRow N) :
    unitCoefficient N 2 0 * axisProfile N (unitPermutation N 0 p).1 = 0 := by
  have hd : ¬ (0 : ℕ).Coprime N := by simp only [Nat.coprime_zero_left]; omega
  simp only [unitCoefficient, ite_eq_right hd, zero_mul]

lemma unit_axis_one (N : ℕ) (p : PrimitiveRow N) :
    unitCoefficient N 2 1 * axisProfile N (unitPermutation N 1 p).1 = axisProfile N p.1 := by
  have he : unitPermutation N 1 p = p := by
    apply Subtype.ext
    funext i
    simp [unitPermutation, primitiveUnitEquiv, scaleResidue, ZMod.unitOfCoprime]
  simp only [unitCoefficient, ite_eq_left (Nat.coprime_one_left N), Nat.cast_one, one_pow, inv_one,
    he, one_mul]

/-- The closed additive identity used for weight-two finite profile inversion. -/
theorem primitive_xConstant_add_tail (N : ℕ) (hN : 3 ≤ N) (p : PrimitiveRow N) :
    xConstant N ((p.1 0).val : ℤ) ((p.1 1).val : ℤ) / (N : ℂ) ^ 2 +
      (Real.pi : ℂ) ^ 2 / (3 * (N : ℂ) ^ 2) = axisProfile N p.1 +
      ∑' n : ℕ, unitCoefficient N 2 (n + 2) * axisProfile N (unitPermutation N (n + 2) p).1 := by
  have hs := unit_axis_summable N (by omega) p
  have h := Summable.sum_add_tsum_nat_add 2 hs
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
  simp only [unit_axis_zero N hN p, unit_axis_one N p, zero_add] at h
  exact (primitive_xConstant_unit_series N hN p).trans h.symm

#print axioms primitive_residue_good
#print axioms unit_axis_term
#print axioms unit_axis_summable
#print axioms primitive_xConstant_unit_series
#print axioms primitive_xConstant_add_tail

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants
