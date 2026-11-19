/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps (git blob 6d253652a372b3777a26cba64fa491415c7d5bbe, sha256 6e39129087e71a5c2f640fc81e5f8bae1f63624e11de1bf63c7b2de7e82a9df5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothCuspRealization
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.SmoothCusp IsDedekindDomain UnramifiedWhittaker HeckeIntegralSeam

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (U : Subgroup (AdelicGL2 (𝓞 K) K))
    (hUv : ∀ kv : GL (Fin 2) (v.adicCompletionIntegers K),
      placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) ∈ U)
    (reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K)
    (hsys : IsHeckeCosetSystem U (heckeGen (𝓞 K) K v) reps)
    (hpure : ∀ j, ∃ m : GL (Fin 2) (v.adicCompletion K), reps j = placeEmbed K v m)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g)
    (a : ℂ) (hφT : IsHeckeCosetEigenfunctionAt K U (heckeGen (𝓞 K) K v) v φ a)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hsupp : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K,
      z = z₁ * z₂ ∧ z₂ ∈ U ∧ ∀ xv : GL (Fin 2) (v.adicCompletion K), z₁ * placeEmbed K v xv = placeEmbed K v xv * z₁)
    (hint : ∀ g : AdelicGL2 (𝓞 K) K, Integrable (fun z => φ (g * z) * f z) (adelicGLHaar (Fin 2) (𝓞 K) K))
    {n : ℕ} (h : Fin n → AdelicGL2 (𝓞 K) K) (c : Fin n → ℂ)
    (hh : ∀ i, ∀ xv : GL (Fin 2) (v.adicCompletion K), h i * placeEmbed K v xv = placeEmbed K v xv * h i) :
    let Φ : AdelicGL2 (𝓞 K) K → ℂ := fun g => ∑ i, c i * rightConv K φ f (g * h i)
    (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
      Φ (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Φ g) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, heckeCosetSum K reps Φ g = a * Φ g) ∧
    IsHeckeCosetEigenfunctionAt K U (heckeGen (𝓞 K) K v) v Φ a := by
  revert K v U hUv reps hsys hpure φ hφU a hφT f hsupp hint n h c hh
  exact @_root_.P2MW.S_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps.solution
