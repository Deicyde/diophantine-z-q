/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isUnit_smul_eq
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isUnit_smul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isUnit_smul_eq
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {s s' : Γ(M, U)} {V : X.Opens}
    (hs : Scheme.Modules.IsFrameOn s V) (hs' : Scheme.Modules.IsFrameOn s' V)
    {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) :
    ∃ u : Γ(X, W), IsUnit u ∧
      u • M.presheaf.map (homOfLE hWU).op s = M.presheaf.map (homOfLE hWU).op s' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isUnit_smul_eq.solution
