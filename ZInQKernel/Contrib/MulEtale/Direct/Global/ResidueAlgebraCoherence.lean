/-
Multiplication-etale construction: ResidueAlgebraCoherence.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Algebra.Tower

noncomputable section
namespace H101DirectGlobalDetection.ResidueAlgebraCoherence

/-- Any S-action on the native residue field coherent with S -> T -> κ(T)
is equal, as an Algebra structure, to the native canonical residue action.
This is actual Algebra.algebra_ext from actual algebraMap equations. -/
theorem algebra_eq_canonical
    (S T : Type*) [CommRing S] [CommRing T] [IsLocalRing T] [Algebra S T]
    (P : Algebra S (IsLocalRing.ResidueField T))
    (hTower : letI := P; IsScalarTower S T (IsLocalRing.ResidueField T)) :
    P = (IsLocalRing.ResidueField.algebra T : Algebra S (IsLocalRing.ResidueField T)) := by
  apply Algebra.algebra_ext
  intro s
  letI := P
  letI : IsScalarTower S T (IsLocalRing.ResidueField T) := hTower
  change algebraMap S (IsLocalRing.ResidueField T) s =
    IsLocalRing.residue T (algebraMap S T s)
  rw [IsScalarTower.algebraMap_apply S T (IsLocalRing.ResidueField T),
    IsLocalRing.ResidueField.algebraMap_eq]

end H101DirectGlobalDetection.ResidueAlgebraCoherence
