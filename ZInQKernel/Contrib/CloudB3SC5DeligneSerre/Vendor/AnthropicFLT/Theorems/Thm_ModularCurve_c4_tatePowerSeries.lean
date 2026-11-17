/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_c4_tatePowerSeries (git blob fe69b349553d8f7e53c0689372a09af2f82c431e, sha256 2984985200dbe98b9c63468b492b3fcfb35e17404daa022cf2c23737ca343d47).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateFormal
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_c4_tatePowerSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open PowerSeries HahnSeries ModularCurve
theorem ModularCurve.c4_tatePowerSeries : tatePowerSeries.c₄ = eisenstein4 := @_root_.P2MW.S_ModularCurve_c4_tatePowerSeries.solution
