/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_heckeDiamondCommuteBar (git blob 01c974bf469cdcb3054d573ffc45201e66d83b47, sha256 89df28e7c222966be60e0af47b0b008813b316ffad31b4f7ccbcb6ed50fedb42).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_heckeDiamondCommuteBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.heckeDiamondCommuteBar (M : ℕ) [NeZero M] :
    ModularCurve.HeckeDiamondCommuteBar M := by
  revert M
  exact @_root_.P2MW.S_ModularCurve_heckeDiamondCommuteBar.solution
