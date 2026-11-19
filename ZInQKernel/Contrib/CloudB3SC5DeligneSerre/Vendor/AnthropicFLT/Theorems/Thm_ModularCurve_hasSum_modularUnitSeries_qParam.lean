/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_qParam (git blob 82cc7d6d74cef62af79d13ae579b449511e85560, sha256 bf72671c6f5e515ee99d406f230ceae5431547adf970fef6fd8c3d3d5cbc3242).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ModularUnit
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_hasSum_modularUnitSeries_qParam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.hasSum_modularUnitSeries_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (((ModularCurve.modularUnitSeries N).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ)) := by
  revert N τ
  exact @_root_.P2MW.S_ModularCurve_hasSum_modularUnitSeries_qParam.solution
