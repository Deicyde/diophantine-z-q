/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral (git blob 52aeb7d2a4080b7f276a8f93d43f426fac792d3f, sha256 d6433ac8f8330046bfa4ab6bc1085fd682f3ab453ddc11130f85830cf58e7702).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_comp_add_right_mem_pureTensorSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral.NumberField.AdelicFourier
open _root_.NumberField.AdelicBox
open _root_.AutomorphicForm
open _root_.IsDedekindDomain
open _root_.MeasureTheory

namespace NumberField
export _root_.NumberField (AdeleRing AdelicBox.adelicBox)
namespace AdelicFourier
export _root_.NumberField.AdelicFourier (fourierIntegral fourierIntegral_zero fourierIntegral_smul fourierIntegral_add fourierIntegral_comp_add_right pureTensorSet schwartzBruhat schwartzBruhat_induction tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet fourierIntegral_mem_schwartzBruhat comp_add_right_mem_pureTensorSet summable_translate_of_mem_schwartzBruhat integrable_of_mem_schwartzBruhat norm_apply_eq_one_of_isGlobalAddChar)
namespace Ws25T
open _root_.NumberField.AdelicFourier
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
  {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)

omit [BorelSpace (AdeleRing (𝓞 F) F)] in

theorem isAddRightInvariant : μ.IsAddRightInvariant := by
  refine ⟨fun y => ?_⟩
  have : (fun v : AdeleRing (𝓞 F) F => v + y) = fun v => y + v := funext fun v => add_comm v y
  rw [this]
  exact map_add_left_eq_self μ y

include hψ in

theorem integrable_fourierIntegrand {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F)
    (w : AdeleRing (𝓞 F) F) :
    Integrable (fun v => ψ (-(v * w)) * f v) μ := by
  have hfi : Integrable f μ := integrable_of_mem_schwartzBruhat F μ hf
  have hk : Continuous fun v : AdeleRing (𝓞 F) F => ψ (-(v * w)) :=
    hψ.continuous.comp ((continuous_id.mul continuous_const).neg)
  refine Integrable.mono' hfi.norm (hk.aestronglyMeasurable.mul hfi.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun v => ?_)
  rw [norm_mul, norm_apply_eq_one_of_isGlobalAddChar F hψ, one_mul]

include hψ in

theorem summable_fourier_side {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F)
    (x : AdeleRing (𝓞 F) F) :
    Summable fun ξ : F =>
      fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
        * ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ * x) := by
  have hF : fourierIntegral ψ μ f ∈ schwartzBruhat F := fourierIntegral_mem_schwartzBruhat F μ hψ hf
  have hS : Summable fun ξ : F => fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
    simpa only [zero_add] using summable_translate_of_mem_schwartzBruhat F hF 0
  refine Summable.of_norm ?_
  have hn : ∀ ξ : F, ‖fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
        * ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ * x)‖
      = ‖fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ)‖ := fun ξ => by
    rw [norm_mul, norm_apply_eq_one_of_isGlobalAddChar F hψ, mul_one]
  simp_rw [hn]
  exact hS.norm

include hψ in

theorem tsum_translate_impl {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F)
    (x : AdeleRing (𝓞 F) F) :
    ∑' ξ : F, f (x + algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ *
          ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
            * ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ * x) := by
  haveI : μ.IsAddRightInvariant := isAddRightInvariant F μ
  set ι := algebraMap F (AdeleRing (𝓞 F) F) with hι
  set C : ℂ := ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ with hC
  revert x
  refine schwartzBruhat_induction
    (p := fun f _ => ∀ x : AdeleRing (𝓞 F) F,
      ∑' ξ : F, f (x + ι ξ) = C * ∑' ξ : F, fourierIntegral ψ μ f (ι ξ) * ψ (ι ξ * x))
    ?_ ?_ ?_ ?_ hf
  ·
    intro f hf x
    have hg : (fun v => f (v + x)) ∈ pureTensorSet F := comp_add_right_mem_pureTensorSet x hf
    have key := tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet F μ hψ hg
    have hFg : fourierIntegral ψ μ (fun v => f (v + x))
        = fun w => ψ (x * w) * fourierIntegral ψ μ f w :=
      fourierIntegral_comp_add_right ψ μ f x
    rw [hFg] at key
    calc ∑' ξ : F, f (x + ι ξ)
        = ∑' ξ : F, f (ι ξ + x) := by simp_rw [add_comm x]
      _ = C * ∑' ξ : F, ψ (x * ι ξ) * fourierIntegral ψ μ f (ι ξ) := key
      _ = C * ∑' ξ : F, fourierIntegral ψ μ f (ι ξ) * ψ (ι ξ * x) := by
          congr 1; refine tsum_congr fun ξ => ?_; rw [mul_comm, mul_comm x]
  ·
    intro x
    simp [fourierIntegral_zero]
  ·
    intro f g hf hg ihf ihg x
    have hIf := integrable_fourierIntegrand F μ hψ hf
    have hIg := integrable_fourierIntegrand F μ hψ hg
    have hL : ∑' ξ : F, (f + g) (x + ι ξ)
        = ∑' ξ : F, f (x + ι ξ) + ∑' ξ : F, g (x + ι ξ) := by
      simp only [Pi.add_apply]
      exact (summable_translate_of_mem_schwartzBruhat F hf x).tsum_add
        (summable_translate_of_mem_schwartzBruhat F hg x)
    have hR : ∑' ξ : F, fourierIntegral ψ μ (f + g) (ι ξ) * ψ (ι ξ * x)
        = ∑' ξ : F, fourierIntegral ψ μ f (ι ξ) * ψ (ι ξ * x)
          + ∑' ξ : F, fourierIntegral ψ μ g (ι ξ) * ψ (ι ξ * x) := by
      have hpt : ∀ ξ : F, fourierIntegral ψ μ (f + g) (ι ξ) * ψ (ι ξ * x)
          = fourierIntegral ψ μ f (ι ξ) * ψ (ι ξ * x)
            + fourierIntegral ψ μ g (ι ξ) * ψ (ι ξ * x) := fun ξ => by
        rw [fourierIntegral_add ψ μ (ι ξ) (hIf (ι ξ)) (hIg (ι ξ)), add_mul]
      simp_rw [hpt]
      exact (summable_fourier_side F μ hψ hf x).tsum_add (summable_fourier_side F μ hψ hg x)
    rw [hL, hR, ihf x, ihg x, mul_add]
  ·
    intro c f hf ih x
    have hpt : ∀ ξ : F, fourierIntegral ψ μ (c • f) (ι ξ) * ψ (ι ξ * x)
        = c * (fourierIntegral ψ μ f (ι ξ) * ψ (ι ξ * x)) := fun ξ => by
      rw [fourierIntegral_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [hpt]
    rw [tsum_mul_left, tsum_mul_left, ih x]
    ring

end NumberField.AdelicFourier.Ws25T

end

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral.NumberField.AdelicFourier
open _root_.AutomorphicForm

theorem solution (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) (x : AdeleRing (𝓞 F) F) :
    ∑' ξ : F, f (x + algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ *
          ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) * ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ * x) :=
  NumberField.AdelicFourier.Ws25T.tsum_translate_impl F μ hψ hf x
