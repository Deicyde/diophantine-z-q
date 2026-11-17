/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_RingTheory_AffineDilatation
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem NeronModelInfra.exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (Y : Set X) (hY : IsClosed Y) (hYs : ∀ y ∈ Y, f y = IsLocalRing.closedPoint R) :
    ∃ (D : Scheme.{u}) (p : D ⟶ X),
      IsAffineHom p ∧ LocallyOfFiniteType p ∧
      (∀ W : X.Opens, (∀ x ∈ W, f x ≠ IsLocalRing.closedPoint R) → IsIso (p ∣_ W)) ∧
      (∀ d : D, f (p d) = IsLocalRing.closedPoint R → p d ∈ Y) ∧
      (∀ (U : X.Opens) (hU : IsAffineOpen U) (π : R),
        IsLocalRing.maximalIdeal R = Ideal.span {π} →
        ∃ e : (↑(p ⁻¹ᵁ U) : Scheme.{u}) ≅
            Spec (CommRingCat.of (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π))))),
          (p ⁻¹ᵁ U).ι ≫ p = e.hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)))))) ≫ hU.fromSpec) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed.solution
