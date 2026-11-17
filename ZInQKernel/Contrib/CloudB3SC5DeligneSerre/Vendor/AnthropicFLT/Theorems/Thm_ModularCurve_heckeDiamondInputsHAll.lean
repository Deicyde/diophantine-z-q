/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_heckeDiamondInputsHAll (git blob 0e1224e958fbd82db02e51ffdc40d956894a0618, sha256 9bb164a7189c5ef4ba1a1198922bde30b36f2df47fb3d284bab0a4d278b90b4f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_heckeDiamondInputsHAll

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.heckeDiamondInputsHAll (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ModularCurve.HeckeDiamondInputsHAll M H := by
  revert M H
  exact @_root_.P2MW.S_ModularCurve_heckeDiamondInputsHAll.solution
