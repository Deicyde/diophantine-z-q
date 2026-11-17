/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_rightConv_rightConv_eq_rightConv_rightConv_comp_inv (git blob de0e7afbcaf24117f0abc0a50d482a976852f40a, sha256 31332e8333998c46c0690d1c178d122283ae5251ee9346bc6cc39fb9236b1ad2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_rightConv_rightConv_eq_rightConv_rightConv_comp_inv

set_option autoImplicit false

open NumberField MeasureTheory AutomorphicForm NumberField.AdelicHaar
open scoped Pointwise

namespace Ws1
namespace L0

theorem main
    (F : Type) [Field F] [NumberField F]
    (φ : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hφ : Continuous φ)
    (f h : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hhc : Continuous h) (hhs : HasCompactSupport h) :
    rightConv F (rightConv F φ f) h = rightConv F φ (rightConv F h fun x => f x⁻¹) := by
  letI : MeasurableSpace (GL (Fin 2) (AdeleRing (𝓞 F) F)) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 F) F)) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SecondCountableTopology (GL (Fin 2) (AdeleRing (𝓞 F) F)) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  funext g

  show (∫ y, (∫ x, φ (g * y * x) * f x ∂μ) * h y ∂μ) = ∫ z, φ (g * z) * (∫ x, h (z * x) * f x⁻¹ ∂μ) ∂μ

  have h1 : ∀ y : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∫ x, φ (g * y * x) * f x ∂μ) = ∫ x, φ (g * x) * f (y⁻¹ * x) ∂μ := by
    intro y
    rw [← integral_mul_left_eq_self (fun x => φ (g * x) * f (y⁻¹ * x)) y]
    simp only [mul_assoc, inv_mul_cancel_left]
  have h2 : ∀ z : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∫ x, h (z * x) * f x⁻¹ ∂μ) = ∫ y, h y * f (y⁻¹ * z) ∂μ := by
    intro z
    rw [← integral_mul_left_eq_self (fun y => h y * f (y⁻¹ * z)) z]
    simp only [mul_inv_rev, inv_mul_cancel_right]
  simp_rw [h1, h2, ← integral_mul_const, ← integral_const_mul]

  have hswap := integral_integral_swap (μ := μ) (ν := μ)
    (f := fun y x => φ (g * x) * f (y⁻¹ * x) * h y) ?_
  · calc (∫ y, ∫ x, φ (g * x) * f (y⁻¹ * x) * h y ∂μ ∂μ)
        = ∫ x, ∫ y, φ (g * x) * f (y⁻¹ * x) * h y ∂μ ∂μ := hswap
      _ = ∫ z, ∫ y, φ (g * z) * (h y * f (y⁻¹ * z)) ∂μ ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun z => integral_congr_ae (ae_of_all _ fun y => ?_))
          simp only []
          ring
  ·
    have hcont : Continuous (Function.uncurry fun y x : GL (Fin 2) (AdeleRing (𝓞 F) F) =>
        φ (g * x) * f (y⁻¹ * x) * h y) := by
      refine ((hφ.comp (continuous_const.mul continuous_snd)).mul
        (hfc.comp ((continuous_fst.inv).mul continuous_snd))).mul (hhc.comp continuous_fst)
    have hsupp : HasCompactSupport (Function.uncurry fun y x : GL (Fin 2) (AdeleRing (𝓞 F) F) =>
        φ (g * x) * f (y⁻¹ * x) * h y) := by
      refine HasCompactSupport.intro (hhs.prod (hhs.mul hfs)) ?_
      rintro ⟨y, x⟩ hyx
      simp only [Function.uncurry_apply_pair]
      by_cases hy : y ∈ tsupport h
      · have hx : x ∉ tsupport h * tsupport f := fun hx => hyx ⟨hy, hx⟩
        have hfx : f (y⁻¹ * x) = 0 := by
          by_contra hne
          exact hx ⟨y, hy, y⁻¹ * x, subset_tsupport _ (Function.mem_support.mpr hne), mul_inv_cancel_left y x⟩
        rw [hfx, mul_zero, zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    exact hcont.integrable_of_hasCompactSupport hsupp

end Ws1.L0

theorem solution
    (F : Type) [Field F] [NumberField F]
    (φ : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hφ : Continuous φ)
    (f h : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hhc : Continuous h) (hhs : HasCompactSupport h) :
    rightConv F (rightConv F φ f) h = rightConv F φ (rightConv F h fun x => f x⁻¹) :=
  Ws1.L0.main F φ hφ f h hfc hfs hhc hhs
