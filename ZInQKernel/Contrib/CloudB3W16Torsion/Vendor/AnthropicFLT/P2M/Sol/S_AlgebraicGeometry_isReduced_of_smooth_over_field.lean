/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_isReduced_of_smooth_over_field. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_isReduced_of_smooth_over_field

set_option autoImplicit false

universe u

open TensorProduct

namespace IsReducedOfSmoothFieldAux

theorem etale_isReduced (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Algebra.Etale K A] : IsReduced A := by
  haveI : Algebra.FormallyUnramified K A := inferInstance
  haveI : Algebra.EssFiniteType K A := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field K A

theorem isStandardSmooth_isReduced_of_isDomain
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] {φ : R →+* A}
    (hφ : φ.IsStandardSmooth) : IsReduced A := by
  obtain ⟨n, g, -, hg⟩ := hφ.exists_etale_mvPolynomial
  letI : Algebra (MvPolynomial (Fin n) R) A := g.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) A := hg.toAlgebra
  haveI : IsReduced
      (FractionRing (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] A) :=
    IsReducedOfSmoothFieldAux.etale_isReduced (FractionRing (MvPolynomial (Fin n) R)) _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight :
      A →ₐ[MvPolynomial (Fin n) R]
        FractionRing (MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] A)
    (Algebra.TensorProduct.includeRight_injective
      (IsFractionRing.injective (MvPolynomial (Fin n) R)
        (FractionRing (MvPolynomial (Fin n) R))))

theorem smooth_isReduced_of_isDomain
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] {φ : R →+* A}
    (hφ : φ.Smooth) : IsReduced A := by
  rw [RingHom.smooth_iff_locally_isStandardSmooth] at hφ
  obtain ⟨s, hs, H⟩ := hφ
  constructor
  intro x hx
  apply Localization.algebraMap_injective_of_span_eq_top s hs
  rw [map_zero]
  funext a
  haveI : IsReduced (Localization.Away a.1) :=
    IsReducedOfSmoothFieldAux.isStandardSmooth_isReduced_of_isDomain (H a.1 a.2)
  simpa using IsReduced.eq_zero _ (hx.map (algebraMap A (Localization.Away a.1)))

end IsReducedOfSmoothFieldAux

section SchemeLevel

open AlgebraicGeometry CategoryTheory

theorem solution {k : Type u} [Field k]
    {Z : Scheme.{u}} {g : Z ⟶ Spec (.of k)} (hg : Smooth g) : IsReduced Z := by
  haveI := hg
  haveI : ∀ i, IsReduced (Z.affineCover.X i) := by
    intro i
    haveI : IsDomain Γ(Spec (CommRingCat.of k), ⊤) :=
      Function.Injective.isDomain _
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.injective
    haveI : _root_.IsReduced ↑Γ(Z.affineCover.X i, ⊤) :=
      IsReducedOfSmoothFieldAux.smooth_isReduced_of_isDomain
        ((HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp
          (inferInstance : Smooth (Z.affineCover.f i ≫ g)))
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover _ Z.affineCover

end SchemeLevel

#print axioms solution
