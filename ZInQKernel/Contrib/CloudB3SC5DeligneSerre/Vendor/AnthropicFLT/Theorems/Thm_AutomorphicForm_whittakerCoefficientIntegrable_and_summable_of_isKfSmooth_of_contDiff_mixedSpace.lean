/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace (git blob 032f5d7e1eeede146ac097a0f7fb18c095763d84, sha256 8e339de72f0082a83a455bea061c796ef6efd9b4916ac53184699d83f3a48bd0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicBox

open scoped Classical in

theorem AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : IsGlobalAddChar K ψ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hleft : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (hsm : IsKfSmooth K φ)
    (harch : ∀ g : AdelicGL2 (𝓞 K) K,
      ContDiff ℝ (Module.finrank ℚ K + 1) (fun z : mixedEmbedding.mixedSpace K =>
        φ (unipotentGL2 (R := AdeleRing (𝓞 K) K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0) * g))) :
    (∀ (α : K) (g : AdelicGL2 (𝓞 K) K),
        WhittakerCoefficientIntegrable K (productionPinsOf K D U gen (adelicBox K)) ψ φ α g) ∧
      ∀ g : AdelicGL2 (𝓞 K) K,
        Summable (fun α : K =>
          whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ φ α g) := by
  revert K D U gen ψ hψ φ hleft hsm harch
  exact @_root_.P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace.solution
