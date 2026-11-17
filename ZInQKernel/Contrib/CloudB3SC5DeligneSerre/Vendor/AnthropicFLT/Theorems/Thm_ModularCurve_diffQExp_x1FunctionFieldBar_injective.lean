/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_diffQExp_x1FunctionFieldBar_injective (git blob b521dd397a4184476d880a368f9606b83e13f41b, sha256 b3992e59a0917e6967c3237baaab960d88f619d77ce11dc433b283bfe1d94f09).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_HeckeDifferential
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_diffQExp_x1FunctionFieldBar_injective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.diffQExp_x1FunctionFieldBar_injective (M : ℕ) [NeZero M] :
    Function.Injective ⇑(ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)) := by
  revert M
  exact @_root_.P2MW.S_ModularCurve_diffQExp_x1FunctionFieldBar_injective.solution
