/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {P P₀ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) (p₀ : P₀ ⟶ Spec (CommRingCat.of T))
    (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (D : P.Opens) (hD : IsAffineOpen D) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p D
    IsNilpotent ((RingHom.ker π).map (algebraMap T' Γ(P, D))) ∧
    ∃ ε : Spec (CommRingCat.of (Γ(P, D) ⧸ (RingHom.ker π).map (algebraMap T' Γ(P, D)))) ≅ ↑(G ⁻¹ᵁ D),
      ε.hom ≫ G ∣_ D ≫ hD.isoSpec.hom =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, D))))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq.solution
