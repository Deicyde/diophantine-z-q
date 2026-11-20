/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_borel_setIntegral_eq_peterssonIntegral_mul_bruhatEisenstein (git blob 0b93ce56be74cf2c1907e31cddbbeef3cf9a0731, sha256 46f35a83299c76459e6dee358387a186a503e3e9d62c68fb62f191b34adeff61).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_PeterssonIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BorelSubgroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_isFundamentalDomain_borel_setIntegral_eq_peterssonIntegral_mul_bruhatEisenstein

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open IsDedekindDomain NumberField.TateGlobal open AutomorphicForm hiding exists_isFundamentalDomain_globalPoints_range existsUnique_bruhatRepresentative_mul_mem_borelSubgroup
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.exists_isFundamentalDomain_borel_setIntegral_eq_peterssonIntegral_mul_bruhatEisenstein
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (_hφsum : ∀ g : AdelicGL2 (𝓞 F) F, Summable fun ξ : F =>
        ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖)
      (x y : AdelicGL2 (𝓞 F) F → ℂ)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        x (globalPoints (𝓞 F) F γ * g) = x g)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        y (globalPoints (𝓞 F) F γ * g) = y g)
      (_hxc : Continuous x) (_hyc : Continuous y)
      (w d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (𝓕 : Set (AdelicGL2 (𝓞 F) F))
      (_h𝓕s : 𝓕 ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
      (_h𝓕 : IsFundamentalDomain (globalPoints (𝓞 F) F).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
      (_hintx : IntegrableOn (fun g => ‖x g‖ ^ 2 *
          (‖φ g‖ + ∑' ξ : F, ‖φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) *
          ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F))
      (_hinty : IntegrableOn (fun g => ‖y g‖ ^ 2 *
          (‖φ g‖ + ∑' ξ : F, ‖φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) *
          ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F)),
    ∃ 𝓕B : Set (AdelicGL2 (𝓞 F) F), MeasurableSet 𝓕B ∧
      IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      IntegrableOn (fun g : AdelicGL2 (𝓞 F) F =>
        ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
            (fun _ => (1 : ℂ)) g) *
          (x g * φ g * (starRingEnd ℂ) (y g) *
            ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ))) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      ∫ g in 𝓕B,
        ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
            (fun _ => (1 : ℂ)) g) *
          (x g * φ g * (starRingEnd ℂ) (y g) *
            ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
        peterssonIntegral F w 𝓕
          (fun g => x g * (φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))) y ∧
      ∫⁻ g in 𝓕B,
        {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
          (fun g => ENNReal.ofReal (‖x g‖ ^ 2 * ‖φ g‖ * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w))) g
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ ∧
      ∫⁻ g in 𝓕B,
        {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
          (fun g => ENNReal.ofReal (‖y g‖ ^ 2 * ‖φ g‖ * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w))) g
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
  revert F
  exact @_root_.P2MW.S_AutomorphicForm_exists_isFundamentalDomain_borel_setIntegral_eq_peterssonIntegral_mul_bruhatEisenstein.solution
