/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_integrableOn_norm_rightConv_sq_mul_archHeight_pow_mul_ideleNorm_rpow_inter_centreCutSiegelSet (git blob 9ef21d91efccf9507a728550fb25928c246044d5, sha256 54526d6cf7c81d214d0481fcd860dff939b2af1b1fddfc75487203ec36160bdd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WindowedSiegelSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_integrableOn_norm_rightConv_sq_mul_archHeight_pow_mul_ideleNorm_rpow_inter_centreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.integrableOn_norm_rightConv_sq_mul_archHeight_pow_mul_ideleNorm_rpow_inter_centreCutSiegelSet
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (w e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') (hd₁' : 0 < d₁') (t : AdelicGL2 (𝓞 K) K) (N : ℕ) :
    IntegrableOn
      (fun g => ‖rightConv K φ f g‖ ^ 2 *
        (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
        ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t) '' centreCutSiegelSet K c' u' d₁' d₂') (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  revert K c u d₁ d₂ T hd hcov χ φ hφ hcont f hf w e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 c' u' d₁' d₂' hc' hd₁' t N
  exact @_root_.P2MW.S_AutomorphicForm_integrableOn_norm_rightConv_sq_mul_archHeight_pow_mul_ideleNorm_rpow_inter_centreCutSiegelSet.solution
