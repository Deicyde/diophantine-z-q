/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.InterfaceD9D10

/-!
# D8: source-independent base-point uniqueness for a localization of Z

Original D8 thin glue, W01/Metamate with agentcloud assistance, 2026-11-15.
This is the generic native localization/Spec argument; the final original
H119 assembly reuses the already-existing HDec.ModelGlue.spec_to_zloc_eq
in TailL, rather than redeclaring that specific original kernel theorem.
No CharZero/model/point-uniqueness premise is added or made into a Fact.
-/

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D8
open CategoryTheory AlgebraicGeometry

/-- Any two maps out of an actual localization of Z agree, since their
restrictions on Z agree. This handles every field-valued base point. -/
theorem ringHom_eq_of_int_localization (M : Submonoid ℤ) (R : Type) [CommRing R]
    [Algebra ℤ R] [IsLocalization M R] {T : Type} [CommRing T]
    (f g : R →+* T) : f = g :=
  IsLocalization.ringHom_ext M (RingHom.ext_int _ _)

/-- Spec base maps are unique by the native fully faithful Spec equivalence.
No chosen default point/map is substituted for the actual two morphisms. -/
theorem specHom_eq_of_int_localization (M : Submonoid ℤ) (R : Type) [CommRing R]
    [Algebra ℤ R] [IsLocalization M R] {T : CommRingCat.{0}}
    (s s' : Spec T ⟶ Spec (CommRingCat.of R)) : s = s' := by
  apply Spec.homEquiv.injective
  ext1
  exact ringHom_eq_of_int_localization M R _ _

#print axioms ringHom_eq_of_int_localization
#print axioms specHom_eq_of_int_localization

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D8
