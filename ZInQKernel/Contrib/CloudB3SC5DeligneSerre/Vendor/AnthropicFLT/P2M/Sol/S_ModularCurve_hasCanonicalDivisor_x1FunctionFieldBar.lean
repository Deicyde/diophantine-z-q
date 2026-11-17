/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_hasCanonicalDivisor_x1FunctionFieldBar (git blob 64ba6bd6b08e1cf2697c857d4544dbd30e800594, sha256 9f0c892bc7416366d4654fb3573a5de16f346de7503447524a2c2b50b05afb5d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_isCurveOver_x1FunctionFieldBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_essFiniteType_x1FunctionFieldBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_hasCanonicalDivisor_x1FunctionFieldBar

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution (M : ℕ) [NeZero M] :
    HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.x1FunctionFieldBar M)) := by
  haveI := ModularCurve.isCurveOver_x1FunctionFieldBar M
  haveI := ModularCurve.essFiniteType_x1FunctionFieldBar M
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
