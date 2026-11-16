/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_exists_hom_glued_comp_toBase_eq_of_comp_eq
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_AffineZariskiSite_exists_hom_glued_comp_toBase_eq_of_comp_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.AffineZariskiSite.exists_hom_glued_comp_toBase_eq_of_comp_eq
    {Y : Scheme.{u}} {F₁ F₂ : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α₁ : (Scheme.AffineZariskiSite.toOpensFunctor Y).op ⋙ Y.presheaf ⟶ F₁}
    {α₂ : (Scheme.AffineZariskiSite.toOpensFunctor Y).op ⋙ Y.presheaf ⟶ F₂}
    (H₁ : α₁.Coequifibered) (H₂ : α₂.Coequifibered) (β : F₂ ⟶ F₁) (hβ : α₂ ≫ β = α₁) :
    ∃ φ : (Scheme.AffineZariskiSite.relativeGluingData H₁).glued ⟶
        (Scheme.AffineZariskiSite.relativeGluingData H₂).glued,
      φ ≫ (Scheme.AffineZariskiSite.relativeGluingData H₂).toBase =
        (Scheme.AffineZariskiSite.relativeGluingData H₁).toBase ∧
      (∀ U : Y.AffineZariskiSite, (Scheme.AffineZariskiSite.relativeGluingData H₁).cover.f U ≫ φ =
        Spec.map (β.app (op U)) ≫ (Scheme.AffineZariskiSite.relativeGluingData H₂).cover.f U) ∧
      (∀ φ' : (Scheme.AffineZariskiSite.relativeGluingData H₁).glued ⟶
          (Scheme.AffineZariskiSite.relativeGluingData H₂).glued,
        (∀ U : Y.AffineZariskiSite, (Scheme.AffineZariskiSite.relativeGluingData H₁).cover.f U ≫ φ' =
          Spec.map (β.app (op U)) ≫ (Scheme.AffineZariskiSite.relativeGluingData H₂).cover.f U) →
        φ' = φ) ∧
      (IsIso β → IsIso φ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_exists_hom_glued_comp_toBase_eq_of_comp_eq.solution
