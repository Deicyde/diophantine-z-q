/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half (git blob e12a034b481f8337ab6a0b70ec4830041d230a75, sha256 edff19ccdce887d03e5cd92a25e2c46554024d2bd212e5b2ad266fc8abe26ce9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)]
    [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (σ : Measure (FiniteAdeleRing (𝓞 F) F))
    [σ.IsAddHaarMeasure] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ)
      (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ)
      (_hs : 1 / 2 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    Integrable (fun t : FiniteAdeleRing (𝓞 F) F =>
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g)) σ := by
  revert F σ
  exact @_root_.P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.solution
