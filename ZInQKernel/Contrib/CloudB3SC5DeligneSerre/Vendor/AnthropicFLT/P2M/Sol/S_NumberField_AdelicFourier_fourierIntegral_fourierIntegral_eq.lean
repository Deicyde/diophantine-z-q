/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq (git blob a62513069f1e5e0ca96e72f1f87ac231e13b98c8, sha256 e585657b54267010ec565b0053c60efb2c558a15f68a8b9d4c5618f45efa65e5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq

open NumberField NumberField.AdelicFourier AutomorphicForm

set_option maxHeartbeats 3200000 in

theorem solution (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) (x : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ (fourierIntegral ψ μ f) x
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ) ^ 2 * f (-x) := by

  have hψu : ∀ y, ‖ψ y‖ = 1 := NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ
  have hInt : ∀ {g : AdeleRing (𝓞 F) F → ℂ} (_ : g ∈ schwartzBruhat F) (w : AdeleRing (𝓞 F) F),
      MeasureTheory.Integrable (fun v => ψ (-(v * w)) * g v) μ := by
    intro g hg w
    have h1 : MeasureTheory.Integrable g μ := NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat F μ hg
    refine h1.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact ((hψ.continuous.comp ((continuous_id.mul continuous_const).neg)).aestronglyMeasurable).mul
        h1.aestronglyMeasurable
    · rw [norm_mul, hψu, one_mul]

  have hadd : ∀ {g₁ g₂ : AdeleRing (𝓞 F) F → ℂ}, g₁ ∈ schwartzBruhat F → g₂ ∈ schwartzBruhat F →
      fourierIntegral ψ μ (g₁ + g₂) = fourierIntegral ψ μ g₁ + fourierIntegral ψ μ g₂ := by
    intro g₁ g₂ h₁ h₂
    funext w
    rw [Pi.add_apply, fourierIntegral_add ψ μ w (hInt h₁ w) (hInt h₂ w)]

  revert x
  refine schwartzBruhat_induction (p := fun g _ => ∀ x, fourierIntegral ψ μ (fourierIntegral ψ μ g) x
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ) ^ 2 * g (-x)) ?_ ?_ ?_ ?_ hf
  ·
    intro g hg x
    exact NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet F μ hψ hg x
  ·
    intro x
    rw [fourierIntegral_zero, fourierIntegral_zero]
    simp
  ·
    intro g₁ g₂ h₁ h₂ ih₁ ih₂ x
    have h₁' := NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat F μ hψ h₁
    have h₂' := NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat F μ hψ h₂
    rw [hadd h₁ h₂, hadd h₁' h₂', Pi.add_apply, ih₁ x, ih₂ x, Pi.add_apply]
    ring
  ·
    intro c g hg ih x
    rw [fourierIntegral_smul, fourierIntegral_smul, Pi.smul_apply, ih x, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring
