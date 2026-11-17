/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top
    {X : Scheme.{u}} {P Q : X.Modules} (μ : P ⟶ Q) {ι : Type v} (𝒱 : ι → X.Opens) (hcov : ⨆ i, 𝒱 i = ⊤)
    (p : ∀ i, Γ(P, 𝒱 i)) (q : ∀ i, Γ(Q, 𝒱 i))
    (hp : ∀ i, Scheme.Modules.IsFrameOn (p i) (𝒱 i)) (hq : ∀ i, Scheme.Modules.IsFrameOn (q i) (𝒱 i))
    (hμ : ∀ i, μ.app (𝒱 i) (p i) = q i) : IsIso μ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top.solution
