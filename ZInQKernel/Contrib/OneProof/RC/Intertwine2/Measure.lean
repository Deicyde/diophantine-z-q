import ZInQKernel.Contrib.OneProof.RC.Intertwine.AdelicFourier
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Finprod

/-! The base cylinder of the restricted product of the determinant-scaled
coordinate Haar measures (tex 8646–8650, 9004–9007). The Haar construction
from the volume of this cylinder is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Intertwine2

open Intertwine MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped BigOperators ENNReal

abbrev FiniteVectors := Fin 3 → RationalFiniteAdeles

abbrev LocalVectors (p : Place) := Fin 3 → ℚ_[p.val]

instance (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
instance (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

instance (p : ℕ) [Fact p.Prime] : MeasurableAdd ℚ_[p] where
  measurable_const_add _ := (continuous_const.add continuous_id).measurable
  measurable_add_const _ := (continuous_id.add continuous_const).measurable

def atPlace (p : Place) (x : FiniteVectors) : LocalVectors p := fun i => x i p

def localLattice (p : Place) : Set (LocalVectors p) :=
  Set.univ.pi fun _ => (PadicInt.subring p.val : Set ℚ_[p.val])

theorem padicIntegers_compact (p : Place) : IsCompact (PadicInt.subring p.val : Set ℚ_[p.val]) := by
  change IsCompact {x : ℚ_[p.val] | ‖x‖ ≤ 1}
  simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
    isCompact_closedBall (0 : ℚ_[p.val]) 1

theorem padicIntegers_open (p : Place) : IsOpen (PadicInt.subring p.val : Set ℚ_[p.val]) :=
  Fact.out (p := ∀ p : Place, IsOpen (PadicInt.subring p.val : Set ℚ_[p.val])) p

theorem localLattice_compact (p : Place) : IsCompact (localLattice p) :=
  isCompact_univ_pi fun _ => padicIntegers_compact p

theorem localLattice_open (p : Place) : IsOpen (localLattice p) :=
  isOpen_set_pi Set.finite_univ fun _ _ => padicIntegers_open p

def padicCompacts (p : Place) : PositiveCompacts ℚ_[p.val] :=
  ⟨⟨PadicInt.subring p.val, padicIntegers_compact p⟩,
    by rw [(padicIntegers_open p).interior_eq]; exact ⟨0, (PadicInt.subring p.val).zero_mem⟩⟩

/-- Coordinate Haar on one copy of `ℚ_p`, giving `ℤ_p` volume one. -/
def padicHaar (p : Place) : Measure ℚ_[p.val] :=
  addHaarMeasure (padicCompacts p)

instance (p : Place) : (padicHaar p).IsAddHaarMeasure := by
  unfold padicHaar
  infer_instance

/-- The local measure in the manuscript's self-dual normalization (8647). -/
def localHaar (a : Fin 3 → ℕ) (p : Place) : Measure (LocalVectors p) :=
  ENNReal.ofReal (Real.sqrt (localNorm (determinant a) p)) •
    Measure.pi (fun _ : Fin 3 => padicHaar p)

instance (a : Fin 3 → ℕ) (p : Place) : (localHaar a p).IsAddLeftInvariant := by
  unfold localHaar
  infer_instance

theorem localHaar_volume (a : Fin 3 → ℕ) (p : Place) :
    localHaar a p (localLattice p) = ENNReal.ofReal (Real.sqrt (localNorm (determinant a) p)) := by
  rw [localHaar, Measure.smul_apply, localLattice, Measure.pi_pi]
  have h : padicHaar p (PadicInt.subring p.val) = 1 :=
    addHaarMeasure_self (K₀ := padicCompacts p)
  simp [h]

theorem localHaar_volume_good (a : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)]
    {p : Place} (hp : p ∉ badPlaces (determinant a)) :
    localHaar a p (localLattice p) = 1 := by
  have hd : determinant a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (2 * a i)
  rw [localHaar_volume, localNorm_good hd hp, Real.sqrt_one, ENNReal.ofReal_one]

theorem rectangular_iff_local (x : FiniteVectors) :
    x ∈ lattice integralAdeles ↔ ∀ p, atPlace p x ∈ localLattice p := by
  change (∀ (i : Fin 3) (p : Place), x i p ∈ PadicInt.subring p.val) ↔ _
  simp only [localLattice, Set.mem_pi, Set.mem_univ, forall_const, atPlace]
  exact forall_comm

/-- Base cylinder mass: the finite product of the local lattice volumes.
Outside `badPlaces (determinant a)` all factors are one. -/
def cylinderMass (a : Fin 3 → ℕ) : ℝ≥0∞ :=
  ∏ p ∈ badPlaces (determinant a), localHaar a p (localLattice p)

/-- Additive Haar on the finite adèles in rectangular coordinates, with
the mass prescribed by the product of the local measures on the base cylinder. -/
def nuF (a : Fin 3 → ℕ) : Measure FiniteVectors :=
  cylinderMass a • coordinateHaar

theorem cylinderMass_eq (a : Fin 3 → ℕ) :
    cylinderMass a = ENNReal.ofReal (finiteVolume a) := by
  unfold cylinderMass finiteVolume
  simp only [localHaar_volume]
  exact (ENNReal.ofReal_prod_of_nonneg fun _ _ => Real.sqrt_nonneg _).symm

theorem nuF_volume (a : Fin 3 → ℕ) :
    nuF a (lattice integralAdeles) = ENNReal.ofReal (finiteVolume a) := by
  rw [nuF, Measure.smul_apply, cylinderMass_eq]
  have h : coordinateHaar (lattice integralAdeles) = 1 :=
    addHaarMeasure_self (K₀ := rectangularCompacts)
  rw [h, smul_eq_mul, mul_one]

theorem nuF_eq_normalizedHaar (a : Fin 3 → ℕ) : nuF a = normalizedHaar a := by
  rw [nuF, cylinderMass_eq, normalizedHaar]

#print axioms padicIntegers_compact
#print axioms padicIntegers_open
#print axioms localLattice_compact
#print axioms localLattice_open
#print axioms localHaar_volume
#print axioms localHaar_volume_good
#print axioms rectangular_iff_local
#print axioms cylinderMass_eq
#print axioms nuF_volume
#print axioms nuF_eq_normalizedHaar

end ZInQ.Manuscript.RC.Intertwine2
