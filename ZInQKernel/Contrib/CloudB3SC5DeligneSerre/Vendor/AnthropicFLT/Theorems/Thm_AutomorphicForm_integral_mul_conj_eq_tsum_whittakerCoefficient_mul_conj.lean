/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj (git blob f408105941ff240ec4c97ed7c224fbfbf3f282e7, sha256 544dd2e57b22d859c1859aaf51e148acb5bf9fe411a885f6da9204677de2bd0d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Probability.ConditionalProbability
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem AutomorphicForm.integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hper₁ : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      φ₁ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ₁ (unipotentGL2 u * g))
    (hcont₁ : Continuous fun x : AdeleRing (𝓞 F) F => φ₁ (unipotentGL2 x * g))
    (hcont₂ : Continuous fun x : AdeleRing (𝓞 F) F => φ₂ (unipotentGL2 x * g))
    (hbdd₂ : ∃ C : ℝ, ∀ x : AdeleRing (𝓞 F) F, ‖φ₂ (unipotentGL2 x * g)‖ ≤ C)
    (hsum₁ : Summable fun α : F =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α g‖) :
    ∫ x, φ₁ (unipotentGL2 x * g) * (starRingEnd ℂ) (φ₂ (unipotentGL2 x * g))
        ∂(productionPinsOf F D U gen (adelicBox F)).ν =
      ∑' α : F, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α g *
        (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₂ α g) := by
  revert F D U gen ψ hψ φ₁ φ₂ g hper₁ hcont₁ hcont₂ hbdd₂ hsum₁
  exact @_root_.P2MW.S_AutomorphicForm_integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj.solution
