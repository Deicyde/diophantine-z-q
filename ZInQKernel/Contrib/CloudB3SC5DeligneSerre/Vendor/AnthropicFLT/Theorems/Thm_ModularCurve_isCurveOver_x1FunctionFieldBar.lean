/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_isCurveOver_x1FunctionFieldBar (git blob 8045627051af7db059c7d3e495fc1f8fc4802a5c, sha256 b43da2cca8df74b0b8fa9ad4096d915153680ad7afbc28bf6e71594b7dd780e8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_isCurveOver_x1FunctionFieldBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open ModularCurve open AlgebraicCurve hiding isCurveOver_of_transcendental_of_perfectField

theorem ModularCurve.isCurveOver_x1FunctionFieldBar (M : ℕ) [NeZero M] :
    IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) := by
  revert M
  exact @_root_.P2MW.S_ModularCurve_isCurveOver_x1FunctionFieldBar.solution
