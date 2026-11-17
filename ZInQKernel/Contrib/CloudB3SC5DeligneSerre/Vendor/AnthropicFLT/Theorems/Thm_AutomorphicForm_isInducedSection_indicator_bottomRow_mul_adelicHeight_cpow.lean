/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow (git blob 48c9cbbf0aa0f15b6f0ed719f30d7332f67de440, sha256 eecff53ce96b4e3b7c917bb875d9aecbd03d6c5cd09eb5a28f810407a5541ae9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchKFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHeight
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHeight NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal Classical

theorem AutomorphicForm.isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ)
      (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ)
      (_hn : ∀ v ∈ S, 0 < n v),
    let φ₀ : AdelicGL2 (𝓞 K) K → ℂ := fun g =>
      if ∀ v ∈ S,
          Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      then ((adelicHeight K g : ℝ) : ℂ) ^ (s + 1 / 2) else 0
    IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s) φ₀ ∧
    Continuous φ₀ ∧ IsArchKFinite K φ₀ ∧ IsKfSmooth K φ₀ ∧
    (∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
      glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
      (∀ v ∈ S, ∀ i j : Fin 2,
        Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
            (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
          ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      φ₀ (g * k) = φ₀ g) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        φ₀ (g * UnramifiedWhittaker.placeEmbed K v
          (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ₀ g) ∧
    (∀ (g k : AdelicGL2 (𝓞 K) K), glFin (𝓞 K) K k = 1 →
      (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
      φ₀ (g * k) = φ₀ g) ∧
    (∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
      (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
      φ₀ k = 0 ∨ φ₀ k = 1) ∧
    φ₀ 1 = 1 := by
  revert K
  exact @_root_.P2MW.S_AutomorphicForm_isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow.solution
