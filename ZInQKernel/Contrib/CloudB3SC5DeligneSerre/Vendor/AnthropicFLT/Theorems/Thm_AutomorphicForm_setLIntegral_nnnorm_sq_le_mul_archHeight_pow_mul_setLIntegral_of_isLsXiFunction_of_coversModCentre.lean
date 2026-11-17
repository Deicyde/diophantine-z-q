/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre (git blob 50a4799291c9f06c47903366223a83a1bc10a0e6, sha256 d12bfcbf38797e9587b96e883347b00fc34fee0f104e87ee69e02a716e2b4eab).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SiegelCovering
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
  AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory
open scoped ENNReal NNReal

theorem AutomorphicForm.setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ)
    (hcont : Continuous φ)
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C)
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') (hd₁' : 0 < d₁') :
    ∃ (T₁ : ℝ) (A : ℕ) (M : ℝ), ∀ x ∈ centreCutSiegelSet K c' u' d₁' d₂',
      T₁ < archHeight K (glArch (𝓞 K) K x) →
        ∫⁻ y in Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
          unipotentGL2 t * x * c) (closure (adelicBox K)) C,
            (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ ENNReal.ofReal (M * archHeight K (glArch (𝓞 K) K x) ^ A) *
            ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
              (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  revert K c u d₁ d₂ T hd hcov χ φ hφ hcont C hC c' u' d₁' d₂' hc' hd₁'
  exact @_root_.P2MW.S_AutomorphicForm_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre.solution
