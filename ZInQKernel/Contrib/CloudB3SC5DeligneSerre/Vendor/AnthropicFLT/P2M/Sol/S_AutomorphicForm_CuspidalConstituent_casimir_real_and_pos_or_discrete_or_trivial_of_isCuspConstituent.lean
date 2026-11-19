/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent (git blob 22b3ec062323d5e4e7fb59a6237453ff7755dada, sha256 cd5b7a76930a2079c42abee512e56cac52a749aeb84472dd941ff478055a657f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_exists_isComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (w : InfinitePlace K) (hw : w.IsReal)
    (lam : ℂ) (hlam : ∀ x ∈ V, IsArchSmoothAt hw x ∧ archCasimirAt hw x = lam • x) :
    lam.im = 0 ∧
      (0 < lam.re ∨
        (∃ k₀ : ℕ, 2 ≤ k₀ ∧ lam = ((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2) ∧
          ∀ (n : ℤ) (N' : Ideal (𝓞 K)) (tys' : AutomorphicForm.ArchTypeFamily K) (x : AdelicGL2 (𝓞 K) K → ℂ),
            N' ≠ ⊥ → x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
              (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
              (adelicBox K)) N' ⊓ archCutSubmodule K tys' →
            (∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) x) →
            HasArchCharacterAt₀ K w (archWeightCharAt hw n) x → x ≠ 0 → (k₀ : ℤ) ≤ |n| ∧ (n - k₀) % 2 = 0) ∨
        (lam = 0 ∧ ∀ x ∈ V, ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℝ),
          Matrix.GeneralLinearGroup.det h = 1 → x (g * archRealGLAt hw h) = x g)) := by
  by_cases hreal : ∀ v : InfinitePlace K, v.IsReal
  · exact AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tys hX hreal w hw lam hlam
  · have hcx : ∃ v : InfinitePlace K, v.IsComplex := by
      push Not at hreal
      obtain ⟨v, hv⟩ := hreal
      exact ⟨v, InfinitePlace.not_isReal_iff_isComplex.1 hv⟩
    exact AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_exists_isComplex
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tys hX hcx w hw lam hlam
