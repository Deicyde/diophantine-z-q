import Mathlib

/-!
# Finite reduced algebras in characteristic zero are étale

B3's stabilizer group construction must not assume its group structure to infer
reducedness of K×K. This file proves the independent finite-reduced algebra step
from Mathlib's Artinian decomposition and separability over a characteristic-zero
field. No Cartier or subgroup-scheme input is used.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

/-- A finite reduced algebra over a characteristic-zero field is étale. -/
theorem etale_of_finite_reduced (k R : Type*) [Field k] [CharZero k]
    [CommRing R] [Algebra k R] [Module.Finite k R] [_root_.IsReduced R] :
    Algebra.Etale k R := by
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  letI (m : MaximalSpectrum R) : Field (R ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  have hfields (m : MaximalSpectrum R) : Module.Finite k (R ⧸ m.asIdeal) ∧
      Algebra.IsSeparable k (R ⧸ m.asIdeal) := by
    haveI : Algebra.IsAlgebraic k (R ⧸ m.asIdeal) := Algebra.IsAlgebraic.of_finite _ _
    exact ⟨inferInstance, inferInstance⟩
  exact (Algebra.Etale.iff_exists_algEquiv_prod k R).mpr
    ⟨MaximalSpectrum R, inferInstance, (fun m => R ⧸ m.asIdeal), inferInstance,
      inferInstance, (IsArtinianRing.equivPi R).restrictScalars k, hfields⟩

/-- The scheme form: a finite reduced scheme over a characteristic-zero field is étale. -/
theorem finite_reduced_scheme_etale {k : Type} [Field k] [CharZero k] {X : Scheme}
    (f : X ⟶ Spec (.of k)) [IsFinite f] [AlgebraicGeometry.IsReduced X] : Etale f := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let e := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  letI : Field Γ(Spec (.of k), ⊤) := (e.isField (Field.toIsField k)).toField
  haveI : CharZero Γ(Spec (.of k), ⊤) :=
    charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  letI : Algebra Γ(Spec (.of k), ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  haveI : Module.Finite Γ(Spec (.of k), ⊤) Γ(X, ⊤) := f.finite_appTop
  haveI : Algebra.Etale Γ(Spec (.of k), ⊤) Γ(X, ⊤) :=
    etale_of_finite_reduced _ _
  apply (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := f)).mpr
  change Algebra.Etale Γ(Spec (.of k), ⊤) Γ(X, ⊤)
  infer_instance

end ZInQ.Contrib.CloudR2Poincare.L4
