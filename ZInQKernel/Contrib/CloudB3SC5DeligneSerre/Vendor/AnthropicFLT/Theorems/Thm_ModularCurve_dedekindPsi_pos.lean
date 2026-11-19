/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_dedekindPsi_pos (git blob bf4ef8bf56b1efca2cd42472c2faf6772b57ba99, sha256 44f60fc6dbcc93a48316d40e5956d90e2900aa32a08e0f32ebf5421151004976).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_dedekindPsi_pos

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.dedekindPsi_pos (N : ℕ) (hN : N ≠ 0) : 0 < dedekindPsi N := by
  revert N hN
  exact @_root_.P2MW.S_ModularCurve_dedekindPsi_pos.solution
