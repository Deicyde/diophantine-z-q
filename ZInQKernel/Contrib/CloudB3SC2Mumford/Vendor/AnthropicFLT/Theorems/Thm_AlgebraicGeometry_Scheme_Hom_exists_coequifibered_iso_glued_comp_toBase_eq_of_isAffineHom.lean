/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    ∃ (H : ((Scheme.AffineZariskiSite.toOpensFunctor Y).op.whiskerLeft f.c).Coequifibered)
      (e : X ≅ (Scheme.AffineZariskiSite.relativeGluingData H).glued),
      e.hom ≫ (Scheme.AffineZariskiSite.relativeGluingData H).toBase = f ∧
      ∀ U : Y.AffineZariskiSite, (f ⁻¹ᵁ U.1).ι ≫ e.hom =
        (f ⁻¹ᵁ U.1).toSpecΓ ≫ (Scheme.AffineZariskiSite.relativeGluingData H).cover.f U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom.solution
