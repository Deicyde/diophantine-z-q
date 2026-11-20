/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_hasSum_smul_modularUnitSeries_inv_qParam (git blob 7d6dde9547f72f408c22a1a300d7c3766fe62629, sha256 6c37f8c39087ffda8581ef52f6d424ae9df5fcabb82d0d6df29b09a47c8dda45).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ModularUnit
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_hasSum_smul_modularUnitSeries_inv_qParam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.hasSum_smul_modularUnitSeries_inv_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((((N : ℚ) ^ 12 • (ModularCurve.modularUnitSeries N)⁻¹).coeff m : ℚ) : ℂ) * Function.Periodic.qParam N (τ : ℂ) ^ m) (ModularForm.discriminant (ModularGroup.S • τ) / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • ModularGroup.S • τ)) := by
  revert N τ
  exact @_root_.P2MW.S_ModularCurve_hasSum_smul_modularUnitSeries_inv_qParam.solution
