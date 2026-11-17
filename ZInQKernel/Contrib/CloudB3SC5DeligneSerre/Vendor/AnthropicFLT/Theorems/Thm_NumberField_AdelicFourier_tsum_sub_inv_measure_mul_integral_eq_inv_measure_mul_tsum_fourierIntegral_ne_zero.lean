/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicFourier_tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero (git blob 6357271a9a47b8cf9ad74fb4cbf8eed220bb5a23, sha256 0cd52f3efd85668c176fc3142de72e587c59cad4ea24c15f30af421be6c5e998).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicFourier_tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField NumberField.AdelicFourier AutomorphicForm
theorem NumberField.AdelicFourier.tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
        - ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ * ∫ v, f v ∂μ
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ *
          ∑' ξ : {ξ : F // ξ ≠ 0}, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  revert F μ ψ hψ f hf
  exact @_root_.P2MW.S_NumberField_AdelicFourier_tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero.solution
