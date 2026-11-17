/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_hasCanonicalDivisor_x1FunctionFieldBar (git blob 5cdf8cf0b09f1b4bfb69cfb38ae3d678d759b0b5, sha256 f9ffbcd21d4ab8d3a7bfcfbd9973dc9589fb05cd5d7754ef9273cd6d1edcf809).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_hasCanonicalDivisor_x1FunctionFieldBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open AlgebraicCurve hiding hasCanonicalDivisor_of_isCurveOver open ModularCurve hiding isCurveOver_x1FunctionFieldBar essFiniteType_x1FunctionFieldBar

theorem ModularCurve.hasCanonicalDivisor_x1FunctionFieldBar (M : ℕ) [NeZero M] :
    HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.x1FunctionFieldBar M)) := by
  revert M
  exact @_root_.P2MW.S_ModularCurve_hasCanonicalDivisor_x1FunctionFieldBar.solution
