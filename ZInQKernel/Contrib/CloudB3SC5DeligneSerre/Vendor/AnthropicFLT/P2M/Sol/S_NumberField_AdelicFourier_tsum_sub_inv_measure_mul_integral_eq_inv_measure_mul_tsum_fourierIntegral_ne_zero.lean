/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero (git blob 893ab3f08a85050274d91d87acdfa6569185189e, sha256 dcd37223b7966dc6380e7db979c878cca260a0bf262c22dc5efb680cbb9d9d0f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero

open NumberField NumberField.AdelicFourier AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
        - ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ * ∫ v, f v ∂μ
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ *
          ∑' ξ : {ξ : F // ξ ≠ 0}, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  have hsum : Summable fun ξ : F ↦ fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
    have := summable_translate_of_mem_schwartzBruhat F
      (fourierIntegral_mem_schwartzBruhat F μ hψ hf) 0
    simpa only [zero_add] using this
  have key : ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) 0)
        + ∑' ξ : {ξ : F // ξ ≠ 0}, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
    rw [← hsum.sum_add_tsum_subtype_compl {0}, Finset.sum_singleton]
    congr 1
    exact tsum_congr_subtype
      (fun ξ : F ↦ fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ)) fun x ↦ by simp
  have h0 : fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) 0) = ∫ v, f v ∂μ := by
    simp [fourierIntegral_def]
  rw [tsum_eq_inv_measure_mul_tsum_fourierIntegral F μ hψ hf, key, h0]
  ring
