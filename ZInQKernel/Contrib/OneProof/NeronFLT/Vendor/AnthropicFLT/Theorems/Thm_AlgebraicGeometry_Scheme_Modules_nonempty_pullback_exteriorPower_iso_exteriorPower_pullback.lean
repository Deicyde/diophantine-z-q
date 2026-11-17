/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-simp] PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_exteriorPower_iso_exteriorPower_pullback {X : Scheme.{u}} (n : ℕ) (U : X.Opens) (M : X.Modules) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.exteriorPower X n).obj M) ≅
      (Scheme.Modules.exteriorPower (U : Scheme.{u}) n).obj ((Scheme.Modules.pullback U.ι).obj M)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback.solution
