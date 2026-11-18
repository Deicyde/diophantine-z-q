import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Models
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Split level weights, tex 8499–8534

Use (y=(1+x)/2), including at odd primes where 2 is a unit. On the support
`y` is in the order, has trace 1, and has two roots `a, 1-a` with unit
difference `2*a-1`. At positive level the quotient selects the root
congruent to the bottom-right entry. Congruence estimates in this coordinate
are provenance (c).
-/

namespace ZInQ.Manuscript.RC.LocalWeights
open Matrix Polynomial

variable {p : ℕ} [Fact p.Prime]

local notation "red" => PadicInt.toZModPow

theorem unit_iff_red_ne_zero (a : ℤ_[p]) : IsUnit a ↔ red 1 a ≠ 0 := by
  rw [← not_iff_not, not_not, PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd]
  simpa using (red_eq_iff p 1 a 0).symm

/-- If two unit-separated branches start at the same residue, their difference
modulo (p^k) is bounded by the difference of the constant terms. -/
theorem branch_congr (k : ℕ) {a b d d' : ℤ_[p]} (ha : a ^ 2 - a + d = 0)
    (hb : b ^ 2 - b + d' = 0) (hu : IsUnit (2 * a - 1))
    (hab : red 1 a = red 1 b) (hd : red k d = red k d') :
    red k a = red k b := by
  have hunit : IsUnit (a + b - 1) := by
    rw [unit_iff_red_ne_zero] at hu ⊢
    simpa [map_sub, map_add, ← hab, two_mul] using hu
  have hf : (a - b) * (a + b - 1) = d' - d := by linear_combination ha - hb
  have h := congrArg (red k : ℤ_[p] →+* ZMod (p ^ k)) hf
  simp only [map_mul, map_sub, hd, sub_self] at h
  exact sub_eq_zero.mp ((hunit.map (red k)).mul_right_cancel (by simpa using h))

/-- Hensel at a simple residue root of (X^2-X+d). -/
theorem lift_branch {a d : ℤ_[p]} (hu : IsUnit (2 * a - 1))
    (h : red 1 (a ^ 2 - a + d) = 0) :
    ∃ b : ℤ_[p], b ^ 2 - b + d = 0 ∧ red 1 b = red 1 a ∧ IsUnit (2 * b - 1) := by
  let F : ℤ_[p][X] := X ^ 2 - X + C d
  have heval (b : ℤ_[p]) : F.aeval b = b ^ 2 - b + d := by simp [F]
  have hderiv (b : ℤ_[p]) : F.derivative.aeval b = 2 * b - 1 := by
    rw [show F.derivative = C (2 : ℤ_[p]) * X - 1 by
      simp only [F, derivative_add, derivative_sub, derivative_pow, derivative_X, derivative_C,
        add_zero, show 2 - 1 = (1 : ℕ) by decide, pow_one, mul_one, Nat.cast_ofNat]]
    simp
  have hn : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [heval, hderiv, PadicInt.isUnit_iff.mp hu, one_pow]
    exact PadicInt.not_isUnit_iff.mp (mt (unit_iff_red_ne_zero _).mp (not_not_intro h))
  obtain ⟨b, hb, hba, hunit, -⟩ := hensels_lemma hn
  refine ⟨b, by simpa only [heval] using hb, (red_eq_iff p 1 b a).mpr ?_, ?_⟩
  · rw [hderiv, PadicInt.isUnit_iff.mp hu] at hba
    simpa only [pow_one] using (PadicInt.norm_lt_one_iff_dvd _).mp hba
  · rw [hderiv, hderiv, PadicInt.isUnit_iff.mp hu] at hunit
    exact PadicInt.isUnit_iff.mpr hunit

/-- The root selected on the level quotient, expressed as an eigenvalue of (y). -/
def LevelRoot {e : ℕ} (y : eichler p e) (a : ℤ_[p]) : Prop :=
  a ^ 2 - a + y.val.det = 0 ∧ IsUnit (2 * a - 1) ∧ red e a = level p e y

/-- The bottom-right entry solves the characteristic equation modulo the level. -/
theorem level_residue_root {e : ℕ} (y : eichler p e) (ht : y.val.trace = 1) :
    red e ((y.val 1 1) ^ 2 - y.val 1 1 + y.val.det) = 0 := by
  have hc : red e (y.val 1 0) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact y.property
  rw [Matrix.trace_fin_two] at ht
  rw [show (y.val 1 1) ^ 2 - y.val 1 1 + y.val.det = -(y.val 0 1 * y.val 1 0) by
    rw [Matrix.det_fin_two]; linear_combination y.val 1 1 * ht]
  simp [hc]

/-- Positive level: one simple residue test detects the split unit support, and
the lift is unique. -/
theorem levelRoot_existsUnique {e : ℕ} (he : 0 < e) (y : eichler p e)
    (ht : y.val.trace = 1) :
    (∃! a, LevelRoot y a) ↔ IsUnit (2 * y.val 1 1 - 1) := by
  have reduce (a b : ℤ_[p]) (h : red e a = red e b) : red 1 a = red 1 b := by
    rw [← PadicInt.cast_toZModPow 1 e he a, ← PadicInt.cast_toZModPow 1 e he b, h]
  have unit_eq (a b : ℤ_[p]) (h : red 1 a = red 1 b) :
      IsUnit (2 * a - 1) ↔ IsUnit (2 * b - 1) := by
    simp only [unit_iff_red_ne_zero, map_sub, map_mul, map_one, h]
  constructor
  · rintro ⟨a, ⟨-, hu, ha⟩, -⟩
    exact (unit_eq _ _ (reduce _ _ ha)).mp hu
  · intro h
    have hmod := reduce ((y.val 1 1) ^ 2 - y.val 1 1 + y.val.det) 0
      ((level_residue_root y ht).trans (map_zero _).symm)
    rw [map_zero] at hmod
    obtain ⟨a, ha, hamod, hau⟩ := lift_branch h hmod
    have hamod' : red e a = level p e y := by
      have hh := branch_congr e ha (show (y.val 1 1) ^ 2 - y.val 1 1 +
          (y.val 1 1 - (y.val 1 1) ^ 2) = 0 by ring) hau hamod
      apply hh
      simpa [map_add, map_sub, map_pow, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using (eq_neg_of_add_eq_zero_right (by
          simpa only [map_add, map_sub, map_pow] using level_residue_root y ht) :
            red e y.val.det = -(red e (y.val 1 1) ^ 2 - red e (y.val 1 1)))
    refine ⟨a, ⟨ha, hau, hamod'⟩, fun b hb => ?_⟩
    apply PadicInt.ext_of_toZModPow.mp
    intro k
    exact branch_congr k hb.1 ha hb.2.1 (reduce _ _ (hb.2.2.trans hamod'.symm)) rfl

/-- The selected branch is unchanged under order-unit conjugation. -/
theorem levelRoot_conj {e : ℕ} (u : (eichler p e)ˣ) (y : eichler p e) (a : ℤ_[p]) :
    LevelRoot ((↑u⁻¹ : eichler p e) * y * (↑u : eichler p e)) a ↔ LevelRoot y a := by
  let v : (Mat ℤ_[p])ˣ := Units.map (eichler p e).val.toMonoidHom u
  have hdet : ((↑u⁻¹ : eichler p e).val * y.val * (↑u : eichler p e).val).det =
      y.val.det := Matrix.det_units_conj' v y.val
  have hlev : level p e ((↑u⁻¹ : eichler p e) * y * (↑u : eichler p e)) =
      level p e y := by
    have hi := congrArg (level p e) (Units.inv_mul u)
    simp only [map_mul, map_one] at hi
    rw [map_mul, map_mul, mul_right_comm, hi, one_mul]
  simp only [LevelRoot, hlev]
  change (_ ^ 2 - _ + ((↑u⁻¹ : eichler p e).val * y.val * (↑u : eichler p e).val).det = 0 ∧
    _ ∧ _) ↔ _
  rw [hdet]

/-- Weighted characteristic function on the affine level model (y=(1+x)/2),
using the character of the selected unit (2a-1). -/
noncomputable def levelWeight {O : Type*} [CommRing O] {e : ℕ}
    (χ : ℤ_[p]ˣ →* Oˣ) (y : eichler p e) : O :=
  open Classical in
  if h : ∃ a, LevelRoot y a ∧ y.val.trace = 1 then
    (χ (Classical.choose_spec h).1.2.1.unit : O)
  else 0

theorem levelWeight_eq {O : Type*} [CommRing O] {e : ℕ} (he : 0 < e)
    (χ : ℤ_[p]ˣ →* Oˣ) {y : eichler p e} (ht : y.val.trace = 1)
    {a : ℤ_[p]} (ha : LevelRoot y a) :
    levelWeight χ y = (χ ha.2.1.unit : O) := by
  classical
  have h : ∃ a, LevelRoot y a ∧ y.val.trace = 1 := ⟨a, ha, ht⟩
  obtain ⟨b, _, hb⟩ := (levelRoot_existsUnique he y ht).mpr
    ((levelRoot_existsUnique he y ht).mp ⟨a, ha, fun c hc => by
      apply PadicInt.ext_of_toZModPow.mp
      intro k
      refine branch_congr k hc.1 ha.1 hc.2.1 ?_ rfl
      rw [← PadicInt.cast_toZModPow 1 e he c, ← PadicInt.cast_toZModPow 1 e he a,
        hc.2.2, ha.2.2]⟩)
  have hb' := (hb h.choose h.choose_spec.1).trans (hb a ha).symm
  have hu : h.choose_spec.1.2.1.unit = ha.2.1.unit := by
    apply Units.ext
    simpa using congrArg (fun z : ℤ_[p] => 2 * z - 1) hb'
  simp only [levelWeight, dite_eq_left h, hu]

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights in
#print axioms unit_iff_red_ne_zero
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms branch_congr
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms lift_branch
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms level_residue_root
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms levelRoot_existsUnique
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms levelRoot_conj
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms levelWeight_eq
