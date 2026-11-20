/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul (git blob 9858d8bc5c4ceec5cccdaa1f75d3e33b5437588d, sha256 3adf9a79285e4a919bc5b57cc872972683369de3aebd8b8a6c3a4b5daf9dacdf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Probability.ConditionalProbability
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox NumberField.AdelicHaar NumberField.AdelicLevel

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem AutomorphicForm.whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (G : AdelicGL2 (𝓞 F) F → ℂ)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F) (h : AdelicGL2 (𝓞 F) F),
      G (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * h) = G (unipotentGL2 u * h))
    (ι : Finset (AdeleRing (𝓞 F) F)) (c : AdeleRing (𝓞 F) F → ℂ)
    (α : F) (a : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F)
    (hcomm : ∀ y ∈ ι, g * unipotentGL2 y = unipotentGL2 y * g)
    (hint : ∀ y ∈ ι, WhittakerCoefficientIntegrable F (productionPinsOf F D U gen (adelicBox F)) ψ
      (fun x => G (x * unipotentGL2 y)) α (diagOne a * g)) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ
        (fun x => ∑ y ∈ ι, c y * G (x * unipotentGL2 y)) α (diagOne a * g) =
      (∑ y ∈ ι, c y * ψ (algebraMap F (AdeleRing (𝓞 F) F) α * ((a : AdeleRing (𝓞 F) F) * y))) *
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ G α (diagOne a * g) := by
  revert F D U gen ψ hψ G hper ι c α a g hcomm hint
  exact @_root_.P2MW.S_AutomorphicForm_whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul.solution
