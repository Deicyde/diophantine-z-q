/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_diamondOneBar_comm (git blob 99816ef02fcf0a791676cfdffbd7ebaeab24ae18, sha256 b7fca65e8617b094755d48b5e9d1ea905e4b42c08d0d74e86d71cda82affcf4a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1Diamond
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_diamondOneBar_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.diamondOneBar_comm (M d e : ℕ) :
    ModularCurve.diamondOneBar M d * ModularCurve.diamondOneBar M e =
      ModularCurve.diamondOneBar M e * ModularCurve.diamondOneBar M d := by
  revert M d e
  exact @_root_.P2MW.S_ModularCurve_diamondOneBar_comm.solution
