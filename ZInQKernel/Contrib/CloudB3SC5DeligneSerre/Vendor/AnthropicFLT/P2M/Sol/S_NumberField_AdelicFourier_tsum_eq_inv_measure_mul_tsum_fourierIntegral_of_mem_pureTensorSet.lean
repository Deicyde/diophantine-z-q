/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet (git blob 09b71215f0e520ddb49d5dc86c373bc5e98a92e8, sha256 97d8c3840180459dc4d8e79adec4c887e60c7b8433578d14394e54c000dc6535).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm MeasureTheory
open scoped Classical ENNReal

noncomputable section

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ *
          ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by

  set c : ℝ≥0∞ := μ (adelicBox F) with hc_def
  have hc_lt : c < ⊤ := by
    obtain ⟨C, hC_cpt, hC_sub⟩ := exists_isCompact_adelicBox_subset F
    exact lt_of_le_of_lt (measure_mono hC_sub) hC_cpt.measure_lt_top
  have hc_pos : 0 < c := by
    obtain ⟨U, hU_open, hU_ne, hU_sub⟩ := exists_isOpen_subset_adelicBox F
    exact lt_of_lt_of_le (hU_open.measure_pos μ hU_ne) (measure_mono hU_sub)
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hc_ne_top : c ≠ ⊤ := hc_lt.ne
  have hcR_ne : (c.toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos hc_ne hc_ne_top).ne'

  set μ' : Measure (AdeleRing (𝓞 F) F) := c⁻¹ • μ with hμ'_def
  have hμ'B : μ' (adelicBox F) = 1 := by
    rw [hμ'_def, Measure.smul_apply, smul_eq_mul, ← hc_def,
      ENNReal.inv_mul_cancel hc_ne hc_ne_top]
  haveI hμ'Haar : μ'.IsAddHaarMeasure := by
    rw [hμ'_def]
    exact MeasureTheory.Measure.IsAddHaarMeasure.smul _
      (ENNReal.inv_ne_zero.mpr hc_ne_top) (ENNReal.inv_ne_top.mpr hc_ne)

  have hμ_eq : μ = c • μ' := by
    rw [hμ'_def, ← smul_assoc, smul_eq_mul,
      ENNReal.mul_inv_cancel hc_ne hc_ne_top, one_smul]

  have hFourier : ∀ w, fourierIntegral ψ μ f w
      = (c.toReal : ℂ) * fourierIntegral ψ μ' f w := by
    intro w
    rw [fourierIntegral_def, fourierIntegral_def, hμ_eq, integral_smul_measure,
      Complex.real_smul]

  simp_rw [hFourier]
  rw [tsum_mul_left, ← mul_assoc, inv_mul_cancel₀ hcR_ne, one_mul]
  exact tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one
    F μ' hμ'B hψ hf
