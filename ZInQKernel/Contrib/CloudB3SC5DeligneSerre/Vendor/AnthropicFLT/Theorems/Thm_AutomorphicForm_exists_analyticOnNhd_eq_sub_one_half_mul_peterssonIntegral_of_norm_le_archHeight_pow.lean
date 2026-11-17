/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_eq_sub_one_half_mul_peterssonIntegral_of_norm_le_archHeight_pow (git blob 2438ccb729bc6e7fb45b372a5d65d1230c74e009, sha256 95cb6e3841db75b1b7845e9659c6294de2dedb0e91fbd25414e97f6a01b110df).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_PeterssonIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WindowedSiegelSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Meromorphic.Order
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_analyticOnNhd_eq_sub_one_half_mul_peterssonIntegral_of_norm_le_archHeight_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.exists_analyticOnNhd_eq_sub_one_half_mul_peterssonIntegral_of_norm_le_archHeight_pow
    (F : Type) [Field F] [NumberField F]
    (w a c u : ℝ) (_hc : 0 < c) (ι : Type) [Fintype ι] (t : ι → AdelicGL2 (𝓞 F) F)
    (𝓕 : Set (AdelicGL2 (𝓞 F) F)) (_h𝓕m : MeasurableSet 𝓕)
    (_h𝓕cov : 𝓕 ⊆ ⋃ i, (· * t i) '' integralWindowedSiegelSet F c u)
    (G : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (_hGan : ∀ g, AnalyticOnNhd ℂ (fun s => G s g) {s : ℂ | a < s.re})
    (_hGc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    (_hGbd : ∀ (C : Set ℂ), IsCompact C → C ⊆ {s : ℂ | a < s.re} → ∀ i : ι,
      ∃ (M : ℝ) (N : ℕ), ∀ s ∈ C, ∀ g ∈ integralWindowedSiegelSet F c u,
        ‖G s (g * t i)‖ ≤ M * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N)
    (x y : AdelicGL2 (𝓞 F) F → ℂ) (_hxc : Continuous x) (_hyc : Continuous y)
    (_hdecay : ∀ (i : ι) (N : ℕ), IntegrableOn
      (fun g => ‖x g‖ * ‖y g‖ * (1 + archHeight F (glArch (𝓞 F) F (g * (t i)⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t i) '' integralWindowedSiegelSet F c u) (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) {s : ℂ | a < s.re} ∧
    ∀ (s₀ : ℂ) (σ₁ : ℝ) (E : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), σ₁ < s.re → G s g = (s - s₀) * E s g) →
      ∀ s : ℂ, σ₁ < s.re → a < s.re →
        (∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
        (s - s₀) * peterssonIntegral F w 𝓕 (fun g => x g * E s g) y := by
  revert F w a c u _hc ι t 𝓕 _h𝓕m _h𝓕cov G _hGan _hGc _hGbd x y _hxc _hyc _hdecay
  exact @_root_.P2MW.S_AutomorphicForm_exists_analyticOnNhd_eq_sub_one_half_mul_peterssonIntegral_of_norm_le_archHeight_pow.solution
