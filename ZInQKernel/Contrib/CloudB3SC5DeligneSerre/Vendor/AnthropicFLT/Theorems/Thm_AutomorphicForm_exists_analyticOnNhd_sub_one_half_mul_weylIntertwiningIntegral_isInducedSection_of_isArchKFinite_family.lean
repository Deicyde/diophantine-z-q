/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family (git blob de837225314efc5c25f20435de6217a888989787, sha256 8507e2676db25004cfca64ec36b64e3651748a1479e2d747e0d085ce48c81cb4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchKFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm Filter Topology
open scoped NNReal

theorem AutomorphicForm.exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    letI := adeleBorel (𝓞 F) F
    ∃ (a : ℝ) (Mreg : ℂ → AdelicGL2 (𝓞 F) F → ℂ), a < 1 / 2 ∧
      (∀ h : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Mreg s h) {s : ℂ | a < s.re}) ∧
      (∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        Mreg s h = (s - 1 / 2) * (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) h) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Mreg p.1 p.2)
        ({s : ℂ | a < s.re} ×ˢ Set.univ) ∧
      (∀ s : ℂ, a < s.re →
        IsInducedSection (𝓞 F) F (etaFst 1 α hα (-s)) (etaSnd 1 α hα (-s)) (Mreg s)) := by
  revert F
  exact @_root_.P2MW.S_AutomorphicForm_exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family.solution
