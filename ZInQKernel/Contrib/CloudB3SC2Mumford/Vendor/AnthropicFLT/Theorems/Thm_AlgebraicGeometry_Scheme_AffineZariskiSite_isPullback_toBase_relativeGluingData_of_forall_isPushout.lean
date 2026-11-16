/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_isPullback_toBase_relativeGluingData_of_forall_isPushout
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isPullback_toBase_relativeGluingData_of_forall_isPushout

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.AffineZariskiSite.isPullback_toBase_relativeGluingData_of_forall_isPushout
    {X : Scheme.{u}} {A : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ A} (H : α.Coequifibered)
    {X' Y : Scheme.{u}} (h : X' ⟶ X) [IsAffineHom h] (g : Y ⟶ X') [IsAffineHom g]
    (φ : Y ⟶ (Scheme.AffineZariskiSite.relativeGluingData H).glued)
    (hφ : φ ≫ (Scheme.AffineZariskiSite.relativeGluingData H).toBase = g ≫ h)

    (r : ∀ U : X.AffineZariskiSite, A.obj (op U) ⟶ Y.presheaf.obj (op (g ⁻¹ᵁ (h ⁻¹ᵁ U.1))))
    (hr : ∀ U : X.AffineZariskiSite,
      (g ⁻¹ᵁ (h ⁻¹ᵁ U.1)).ι ≫ φ =
        (g ⁻¹ᵁ (h ⁻¹ᵁ U.1)).toSpecΓ ≫ Spec.map (r U) ≫ (Scheme.AffineZariskiSite.relativeGluingData H).cover.f U)

    (hpo : ∀ U : X.AffineZariskiSite,
      IsPushout (α.app (op U)) (h.app U.1) (r U) (g.app (h ⁻¹ᵁ U.1))) :
    IsPullback φ g (Scheme.AffineZariskiSite.relativeGluingData H).toBase h := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isPullback_toBase_relativeGluingData_of_forall_isPushout.solution
