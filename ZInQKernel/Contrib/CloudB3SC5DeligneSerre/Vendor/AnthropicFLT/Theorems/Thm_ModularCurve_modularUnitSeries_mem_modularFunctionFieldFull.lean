/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull (git blob e53cd2f8f1801ca6a6e2024ffdc1275fc44d568a, sha256 140d8168fd9c62871effb0c0d47b48a849bafdb46bbb60d7424a7766f693a053).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ModularUnit
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull (N : ℕ) [NeZero N] : ModularCurve.modularUnitSeries N ∈ ModularCurve.modularFunctionFieldFull N := by
  revert N
  exact @_root_.P2MW.S_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull.solution
