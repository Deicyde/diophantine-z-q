/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le (git blob 6c9624e774c7918a02a8af6acbed37f06598bcae, sha256 eabc84ba0b4a0c9d79a7fcc10c0a6f8184d81eebc90a629792da32e6283e350d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel open AutomorphicForm hiding whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul sum_norm_whittakerCoefficient_sq_le_integral_norm_sq integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (x y : AdelicGL2 (𝓞 F) F → ℂ)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      x (globalPoints (𝓞 F) F γ * g) = x g)
    (hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      y (globalPoints (𝓞 F) F γ * g) = y g)
    (hxc : Continuous x) (hyc : Continuous y)
    (hx0 : ∀ g, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 0 g = 0)
    (hxW : ∀ g, Summable fun a : F =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x a g‖)
    (g : AdelicGL2 (𝓞 F) F) :
    (Summable fun a : Fˣ =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖ *
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖) ∧
    (∑' a : Fˣ,
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖ *
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖) ≤
      Real.sqrt (∫ u, ‖x (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) *
        Real.sqrt (∫ u, ‖y (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) ∧
    ∫ u, x (unipotentGL2 u * g) * (starRingEnd ℂ) (y (unipotentGL2 u * g))
        ∂(productionPinsOf F D U gen (adelicBox F)).ν =
      ∑' a : Fˣ,
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
            (globalPoints (𝓞 F) F (diagOne a) * g) *
          (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
            (globalPoints (𝓞 F) F (diagOne a) * g)) := by
  revert F D U gen ψ hψ x y hxG hyG hxc hyc hx0 hxW g
  exact @_root_.P2MW.S_AutomorphicForm_integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le.solution
