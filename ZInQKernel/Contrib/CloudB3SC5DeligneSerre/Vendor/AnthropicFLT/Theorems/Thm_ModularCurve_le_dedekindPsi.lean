/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_le_dedekindPsi (git blob ab327f8abd28b9979cbfb104ca5bb00ff77193ae, sha256 e681d546b6f6c034de0639a26c95f32e35ce4e9525d8faf95029f602ac9a931b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_le_dedekindPsi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.le_dedekindPsi (N : ℕ) (hN : N ≠ 0) : N ≤ dedekindPsi N := by
  revert N hN
  exact @_root_.P2MW.S_ModularCurve_le_dedekindPsi.solution
