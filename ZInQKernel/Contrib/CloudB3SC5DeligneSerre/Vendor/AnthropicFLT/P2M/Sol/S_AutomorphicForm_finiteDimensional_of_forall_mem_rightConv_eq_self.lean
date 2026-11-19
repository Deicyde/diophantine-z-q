/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_finiteDimensional_of_forall_mem_rightConv_eq_self (git blob a3a62b99f589679d47d317759e8011f8d124eae7, sha256 ce93872953a546dfb0afe77dbe5be2f15983bc75f0d45935d010e0abf5158e9b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SiegelCovering
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_SiegelVolume
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_MeasureTheory_finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_finiteDimensional_of_forall_mem_rightConv_eq_self

set_option autoImplicit false
open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hE : ∀ φ ∈ E, IsSmoothCuspAutomorphicFnAt F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ φ ∧
      Continuous φ ∧ rightConv F φ f = φ) :
    FiniteDimensional ℂ ↥E := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F

  have hDm : MeasurableSet (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
    refine MeasurableSet.biUnion T.countable_toSet fun x _ => ?_
    rw [Set.image_mul_right]
    exact measurable_mul_const _ (measurableSet_centreCutSiegelSet c u d₁ d₂)
  have hvol : (adelicGLHaar (Fin 2) (𝓞 F) F) (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ≠ ⊤ :=
    (MeasureTheory.measure_biUnion_finset_image_mul_right_lt_top (adelicGLHaar (Fin 2) (𝓞 F) F) _
      (SiegelVolume.measure_centreCutSiegelSet_lt_top (adelicGLHaar (Fin 2) (𝓞 F) F) hc u hd₁ d₂) T).ne

  obtain ⟨C, hC⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
      F c u d₁ d₂ T hc hd₁ hd hcov ξ f hf

  refine (MeasureTheory.finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict
    (adelicGLHaar (Fin 2) (𝓞 F) F) _ hDm hvol E ?_ ?_ C ?_).1
  ·
    intro φ hφ
    exact (hE φ hφ).2.1.aestronglyMeasurable
  ·
    intro φ hφ h0
    exact AutomorphicForm.eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero
      F _ _ _ _ ξ φ (hE φ hφ).1.1 _ hcov h0
  ·
    intro φ hφ x hx
    have h := hC φ (hE φ hφ).1 (hE φ hφ).2.1 x hx
    rwa [(hE φ hφ).2.2] at h
