/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top
    {X : Scheme.{u}} (M N : X.Modules) {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (f : ∀ (W : X.Opens), (∃ i, W ≤ U i) → (Γ(M, W) →ₗ[Γ(X, W)] Γ(N, W)))
    (hf : ∀ (W W' : X.Opens) (hW : ∃ i, W ≤ U i) (h : W' ≤ W) (x : Γ(M, W)),
      N.presheaf.map (homOfLE h).op (f W hW x) = f W' (hW.imp fun _ hi => h.trans hi) (M.presheaf.map (homOfLE h).op x)) :
    ∃! F : M ⟶ N, ∀ (W : X.Opens) (hW : ∃ i, W ≤ U i) (x : Γ(M, W)), F.app W x = f W hW x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top.solution
