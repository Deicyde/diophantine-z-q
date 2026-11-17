/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv (git blob cd4100e2e9391b417230e08f4ca173bee21c1f79, sha256 8709812cfe37990a8a27e2b192f6d07df00cec75b29b7302363c5c718973c5cd).
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
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv

set_option autoImplicit false

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : IsIntegral (Algebra.adjoin ℚ {ModularCurve.jq}) (ModularCurve.modularUnitSeries ℓ)⁻¹ := by
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  refine ModularCurve.isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant ℓ
    (ModularCurve.modularUnitSeries ℓ)⁻¹ (((ℓ : ℚ) ^ 12)⁻¹ • ModularCurve.modularUnitSeries ℓ)
    (fun τ => ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)
      / ModularForm.discriminant τ)
    (fun τ => ModularCurve.hasSum_modularUnitSeries_inv_qParam ℓ τ)
    (fun τ => ModularCurve.hasSum_smul_modularUnitSeries_qParam ℓ τ)
    (fun γ hγ τ => ?_)
  show ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • γ • τ)
      / ModularForm.discriminant (γ • τ)
    = ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ) / ModularForm.discriminant τ
  have h := congrArg Inv.inv
    (ModularCurve.discriminant_div_discriminant_heckeDiagMatrix_smul ℓ γ hγ τ)
  rwa [inv_div, inv_div] at h
