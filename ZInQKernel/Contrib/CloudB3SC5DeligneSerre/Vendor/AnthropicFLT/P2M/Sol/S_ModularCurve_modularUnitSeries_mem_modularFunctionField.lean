/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_modularUnitSeries_mem_modularFunctionField (git blob d33ad5974f63814cbf71cfe4c85c80b4a8cd39e2, sha256 db0e5b76f1ddac533d41c88aa22c258379a0ecfd274af25f85c172d9240a76ce).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ModularUnit
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_qParam
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_hasSum_smul_modularUnitSeries_inv_qParam
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_inv_qParam
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_hasSum_smul_modularUnitSeries_qParam
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_mem_modularFunctionField_of_hasSum_of_gamma0_invariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_modularUnitSeries_mem_modularFunctionField

set_option autoImplicit false

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : ModularCurve.modularUnitSeries ℓ ∈ ModularCurve.modularFunctionField ℓ := by
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  exact ModularCurve.mem_modularFunctionField_of_hasSum_of_gamma0_invariant ℓ
    (ModularCurve.modularUnitSeries ℓ) ((ℓ : ℚ) ^ 12 • (ModularCurve.modularUnitSeries ℓ)⁻¹)
    (fun τ => ModularForm.discriminant τ
      / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))
    (fun τ => ModularCurve.hasSum_modularUnitSeries_qParam ℓ τ)
    (fun τ => ModularCurve.hasSum_smul_modularUnitSeries_inv_qParam ℓ τ)
    (fun γ hγ τ => ModularCurve.discriminant_div_discriminant_heckeDiagMatrix_smul ℓ γ hγ τ)
