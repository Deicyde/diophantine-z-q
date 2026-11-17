/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_j_tateLaurent (git blob c509b0730543ea2bdc08ab62cbbdec52ac74c5b1, sha256 758383e1516c770c69abb8a50c3b17d11bb97400014d6c30ce2b1830c8c01edb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateFormal
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_j_tateLaurent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open PowerSeries HahnSeries ModularCurve
theorem ModularCurve.j_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).j = jqModC K := by
  revert K
  exact @_root_.P2MW.S_ModularCurve_j_tateLaurent.solution
