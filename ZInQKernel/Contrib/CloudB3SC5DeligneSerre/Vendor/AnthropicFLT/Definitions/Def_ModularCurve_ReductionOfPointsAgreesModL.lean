/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL (git blob 9c60952439c892c1d501de911a7fe23d813e2604, sha256 b7bba5708d08c5719c73e5353209b1fa6041ca25ef28373c8c6d13851c9893a8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ReductionModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace ModularCurve

def ReductionOfPointsAgreesModL (p : ℕ) [NeZero p]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {R : Type} [CommRing R] {J : Scheme.{0}} (f : J ⟶ Spec (CommRingCat.of R))
    (σ : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of R))
    (ptsGen : JZero p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ σ) f)
    (ptsSp : JZeroC (IsLocalRing.ResidueField ↥A) p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ σ) f) : Prop :=
  ∀ x : JZero p, ∃ xA : SchemeHomOver σ f,
    schemeHomOverComp (Spec.map (CommRingCat.ofHom A.subtype)) rfl xA = ptsGen x ∧
    schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) rfl xA
      = ptsSp (reductionModL A p x)

theorem reductionOfPointsAgreesModL_iff (p : ℕ) [NeZero p]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {R : Type} [CommRing R] {J : Scheme.{0}} (f : J ⟶ Spec (CommRingCat.of R))
    (σ : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of R))
    (ptsGen : JZero p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ σ) f)
    (ptsSp : JZeroC (IsLocalRing.ResidueField ↥A) p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ σ) f) :
    ReductionOfPointsAgreesModL p A f σ ptsGen ptsSp ↔
      ∀ x : JZero p, ∃ xA : SchemeHomOver σ f,
        schemeHomOverComp (Spec.map (CommRingCat.ofHom A.subtype)) rfl xA = ptsGen x ∧
        schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) rfl xA
          = ptsSp (reductionModL A p x) :=
  Iff.rfl

end ModularCurve

end
