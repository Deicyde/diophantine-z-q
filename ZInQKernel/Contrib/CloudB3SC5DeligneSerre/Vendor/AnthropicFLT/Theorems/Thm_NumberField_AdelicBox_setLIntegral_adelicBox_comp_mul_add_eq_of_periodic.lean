/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicBox_setLIntegral_adelicBox_comp_mul_add_eq_of_periodic (git blob 6a52ee86e0849ef96b69bd394b075e7ac115ca1e, sha256 4644a8ff0e2c11a8991cece9af2e2f2bd7a66db1b6d1eb6b20955ad5d809f22f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicBox_setLIntegral_adelicBox_comp_mul_add_eq_of_periodic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic
    (F : Type) [Field F] [NumberField F]
    (h : AdeleRing (𝓞 F) F → ℝ≥0∞) (hh : Measurable h)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F), h (algebraMap F (AdeleRing (𝓞 F) F) β + u) = h u)
    (a : Fˣ) (u₀ : AdeleRing (𝓞 F) F) :
    ∫⁻ u in adelicBox F, h (algebraMap F (AdeleRing (𝓞 F) F) a * u + u₀) ∂(adelicAddHaar (𝓞 F) F) =
      ∫⁻ u in adelicBox F, h u ∂(adelicAddHaar (𝓞 F) F) := by
  revert F h hh hper a u₀
  exact @_root_.P2MW.S_NumberField_AdelicBox_setLIntegral_adelicBox_comp_mul_add_eq_of_periodic.solution
