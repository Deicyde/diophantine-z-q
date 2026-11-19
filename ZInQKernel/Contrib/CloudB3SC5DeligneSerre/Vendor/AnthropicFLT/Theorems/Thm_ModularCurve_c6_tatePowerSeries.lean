/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_c6_tatePowerSeries (git blob ab53447c64209747c5e530c509337b93084eb417, sha256 3fb61ce2bec962a31becf299db9c9eb7c4d7e941422ce168fc29bd25831b4693).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateFormal
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_c6_tatePowerSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open PowerSeries HahnSeries ModularCurve
theorem ModularCurve.c6_tatePowerSeries : tatePowerSeries.c₆ = -eisenstein6 := @_root_.P2MW.S_ModularCurve_c6_tatePowerSeries.solution
