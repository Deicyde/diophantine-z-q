/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq (git blob 5150e05d6e03977c7e6d522d058338584e93845d, sha256 5568cbcca253ae69e26b0095d8c04ffc53f74f89464c095f480254a99c7b3461).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups
open ModularCurve

theorem ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq
    (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ)) :
    ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ) = ModularCurve.qExpFunctionFieldC L Γ := by
  revert L Γ
  exact @_root_.P2MW.S_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq.solution
