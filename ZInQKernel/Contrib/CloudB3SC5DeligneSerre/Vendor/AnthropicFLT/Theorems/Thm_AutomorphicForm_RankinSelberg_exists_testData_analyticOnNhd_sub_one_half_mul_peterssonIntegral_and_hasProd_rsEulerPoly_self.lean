/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_RankinSelberg_exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self (git blob cb0bffe58e19011b4be847183531629023cf0b97, sha256 5743d17cb15b05260d40005fa1444d4ce09ec58f22df09f189e1161a7a75c61f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchKFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_PeterssonIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_RankinSelberg_exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
      (_hc : 0 < c) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (_hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
      (Θ : HeckeEigensystem K ℂ)
      (R : SmoothCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
      (_hR : IsGenuineCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
      (tys : AutomorphicForm.ArchTypeFamily K)
      (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
      (_hV : IsCuspConstituent K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar V)
      (_hRV : R.toFun ∈ V ⊓ levelInvariantSubmodule K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.level ⊓ archCutSubmodule K tys),
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (f : AdelicGL2 (𝓞 K) K → ℂ) (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (w e₁ e₂ a σ₀ : ℝ) (C : ℂ) (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (A L ζi : ℂ → ℂ),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet) ∧
      IsFactorizableTestFn K f ∧
      (∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s)) ∧
      (∀ s, IsArchKFinite K (φ s)) ∧ (∀ s, IsKfSmooth K (φ s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => φ s g)) ∧
      0 < e₁ ∧ e₁ < e₂ ∧
      IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) ∧
      a < 1 / 2 ∧ 1 / 2 < σ₀ ∧ C ≠ 0 ∧
      AnalyticOnNhd ℂ A {s : ℂ | a < s.re} ∧
      (∀ s : ℂ, 1 / 2 < s.re →
        A s = (s - 1 / 2) * peterssonIntegral K w 𝓕
          (fun g => rightConv K R.toFun f g * (φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g))) (rightConv K R.toFun f)) ∧
      A (1 / 2) ≠ 0 ∧

      AnalyticOnNhd ℂ (fun s : ℂ => RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ s) w e₁ e₂)
        {s : ℂ | a < s.re} ∧
      (∀ σ : ℝ, a < σ →
        (RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ σ) w e₁ e₂).im = 0 ∧
        0 < (RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ σ) w e₁ e₂).re) ∧

      AnalyticOnNhd ℂ ζi {s : ℂ | a < s.re} ∧
      (∀ s : ℂ, a < s.re → ζi s ≠ 0 ∧
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) (ζi s)) ∧
      (∀ σ : ℝ, a < σ → (ζi σ).im = 0 ∧ 0 < (ζi σ).re) ∧

      AnalyticOnNhd ℂ L {s : ℂ | σ₀ < s.re} ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + 1 / 2))))⁻¹) (L s) ∧
        peterssonIntegral K w 𝓕
          (fun g => rightConv K R.toFun f g * (φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g))) (rightConv K R.toFun f) =
        C * RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ s) w e₁ e₂ *
          ζi s * L s) := by
  revert K
  exact @_root_.P2MW.S_AutomorphicForm_RankinSelberg_exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self.solution
