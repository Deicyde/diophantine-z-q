/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_inv_qParam (git blob 5c1f3dfac07bd5c74a30fb81d62879e263b67f44, sha256 0746a79eb752577f6de7052dc8cf21e760306b6598a2a5deb474f366c8a04fd1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ModularUnit
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_hasSum_modularUnitSeries_inv_qParam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.hasSum_modularUnitSeries_inv_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((((ModularCurve.modularUnitSeries N)⁻¹).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) / ModularForm.discriminant τ) := by
  revert N τ
  exact @_root_.P2MW.S_ModularCurve_hasSum_modularUnitSeries_inv_qParam.solution
