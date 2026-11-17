/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_diamondHBar_mul (git blob 95d89bb0203e30c91cd574f528b21b99ea55ec4d, sha256 6cc004d97e1cf501876ca8342f3516031503a026a53da5aca57dbd3dcb66d358).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_diamondHBar_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem ModularCurve.diamondHBar_mul (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (d d' : (ZMod M)ˣ) (x : ModularCurve.JH M H) :
    ModularCurve.diamondHBar M H (d * d') x =
      ModularCurve.diamondHBar M H d (ModularCurve.diamondHBar M H d' x) := by
  revert M H d d' x
  exact @_root_.P2MW.S_ModularCurve_diamondHBar_mul.solution
