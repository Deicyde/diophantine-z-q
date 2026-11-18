import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.Positivity

/-!
# The split local orders for Appendix F

The local coordinates consumed by the weights (tex 8462–8465, 8496–8534, 8536).
The lattice and quotient coordinates below spell out the cyclic quotient (provenance (c)).
-/

namespace ZInQ.Manuscript.RC.LocalWeights

open Matrix
open scoped Topology

abbrev Mat (A : Type*) := Matrix (Fin 2) (Fin 2) A

variable (p : ℕ) [Fact p.Prime]

/-- The lower-left-entry model at level (p^e); at (e=0) it is the full matrix order. -/
def eichler (e : ℕ) : Subalgebra ℤ_[p] (Mat ℤ_[p]) where
  carrier := {x | (p : ℤ_[p]) ^ e ∣ x 1 0}
  add_mem' hx hy := dvd_add hx hy
  zero_mem' := dvd_zero _
  mul_mem' {x y} hx hy := by
    change _ ∣ (x * y) 1 0
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact dvd_add (dvd_mul_of_dvd_left hx _) (dvd_mul_of_dvd_right hy _)
  one_mem' := by simp
  algebraMap_mem' r := by
    change _ ∣ (algebraMap ℤ_[p] (Mat ℤ_[p]) r) 1 0
    simp [Matrix.algebraMap_matrix_apply]

@[simp] theorem eichler_zero : eichler p 0 = ⊤ := by
  ext x
  simp [eichler]

/-- The entry (x_{11}) on (mathbb Z_p^2/
(mathbb Z_p e_0 + p^e mathbb Z_p e_1)), in the coordinate given by (e_1). -/
noncomputable def level (e : ℕ) : eichler p e →+* ZMod (p ^ e) where
  toFun x := PadicInt.toZModPow e (x.val 1 1)
  map_zero' := map_zero _
  map_one' := by simp
  map_add' _ _ := map_add _ _ _
  map_mul' x y := by
    have hc : PadicInt.toZModPow e (x.val 1 0) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
      exact x.property
    change PadicInt.toZModPow e ((x.val * y.val) 1 1) = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, hc]

/-- Quotient compatibility: reduction of the bottom coordinate intertwines the lattice
action with multiplication by `level x`. -/
theorem level_mulVec (e : ℕ) (x : eichler p e) (v : Fin 2 → ℤ_[p]) :
    PadicInt.toZModPow e (x.val.mulVec v 1) =
      level p e x * PadicInt.toZModPow e (v 1) := by
  have hc : PadicInt.toZModPow e (x.val 1 0) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact x.property
  change PadicInt.toZModPow e _ = PadicInt.toZModPow e _ * PadicInt.toZModPow e _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc]

/-- The quotient coordinate reaches every residue. Its kernel is the defining lattice. -/
theorem level_coordinate (e : ℕ) :
    Function.Surjective (fun v : Fin 2 → ℤ_[p] => PadicInt.toZModPow e (v 1)) ∧
      ∀ v : Fin 2 → ℤ_[p], PadicInt.toZModPow e (v 1) = 0 ↔ (p : ℤ_[p]) ^ e ∣ v 1 := by
  refine ⟨?_, fun v => ?_⟩
  · intro a
    obtain ⟨r, hr⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow e) a
    exact ⟨fun _ => r, hr⟩
  · rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

/-- Trace-zero part of the integral or rational model. -/
abbrev TraceZero (A : Type*) [AddCommMonoid A] := {x : Mat A // x.trace = 0}

/-- For the split branch the sibling supplies the completed algebra coordinates and the
order coordinates, and identifies their two inclusions. In applications `R` is the order
after tensoring with `ℤ_[p]` and `B` is the algebra after tensoring with `ℚ_[p]`. -/
structure SplitCoordinates (e : ℕ) (R B : Type*) [Ring R] [Ring B]
    [Algebra ℤ_[p] R] [Algebra ℚ_[p] B] (incl : R →+* B) where
  order : R ≃ₐ[ℤ_[p]] eichler p e
  ambient : B ≃ₐ[ℚ_[p]] Mat ℚ_[p]
  compatible : ∀ x : R, ambient (incl x) =
    (order x).val.map (PadicInt.Coe.ringHom (p := p))

/-- Good-prime integral support, viewed inside the rational trace-zero space. -/
noncomputable def goodWeight {O : Type*} [Zero O] [One O] (x : TraceZero ℚ_[p]) : O :=
  open Classical in
  if ∀ i j, x.val i j ∈ PadicInt.subring p then 1 else 0

theorem goodWeight_congr {O : Type*} [Zero O] [One O] (x y : TraceZero ℚ_[p])
    (h : ∀ i j, x.val i j - y.val i j ∈ PadicInt.subring p) :
    goodWeight p x = (goodWeight p y : O) := by
  classical
  have he : (∀ i j, x.val i j ∈ PadicInt.subring p) ↔
      (∀ i j, y.val i j ∈ PadicInt.subring p) := by
    constructor
    · intro hx i j
      simpa using (PadicInt.subring p).sub_mem (hx i j) (h i j)
    · intro hy i j
      simpa using (PadicInt.subring p).add_mem (h i j) (hy i j)
  simp only [goodWeight, he]

/-- Congruence modulo (p^k), in its divisibility form. -/
theorem red_eq_iff (k : ℕ) (a b : ℤ_[p]) :
    PadicInt.toZModPow k a = PadicInt.toZModPow k b ↔ (p : ℤ_[p]) ^ k ∣ a - b := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton]

/-- Reduction fibers are open. This also covers (k=0), the single fiber. -/
theorem red_locallyConstant (k : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow k : ℤ_[p] → ZMod (p ^ k)) := by
  apply IsLocallyConstant.iff_isOpen_fiber_apply.mpr
  intro a
  have he : (PadicInt.toZModPow k : ℤ_[p] → ZMod (p ^ k)) ⁻¹'
      {PadicInt.toZModPow k a} = Metric.closedBall a ((p : ℝ) ^ (-(k : ℤ))) := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_closedBall, dist_eq_norm]
    rw [red_eq_iff, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
  rw [he]
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  exact IsUltrametricDist.isOpen_closedBall _ (ne_of_gt (zpow_pos hp _))

/-- Entrywise reduction, also used to transport the weights under multiplication. -/
noncomputable def redMat (k : ℕ) : Mat ℤ_[p] →+* Mat (ZMod (p ^ k)) :=
  (PadicInt.toZModPow k).mapMatrix

theorem redMat_locallyConstant (k : ℕ) : IsLocallyConstant (redMat p k) := by
  apply IsLocallyConstant.iff_isOpen_fiber_apply.mpr
  intro a
  have he : redMat p k ⁻¹' {redMat p k a} =
      ⋂ i : Fin 2, ⋂ j : Fin 2, (fun x : Mat ℤ_[p] => x i j) ⁻¹'
        {b | PadicInt.toZModPow k b = PadicInt.toZModPow k (a i j)} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h i j => congrFun (congrFun h i) j, Matrix.ext⟩
  rw [he]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    ((red_locallyConstant p k).isOpen_fiber _).preimage (continuous_apply_apply i j)

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights in
#print axioms eichler_zero
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms level_mulVec
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms level_coordinate
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms goodWeight_congr
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms red_eq_iff
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms red_locallyConstant
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms redMat_locallyConstant
