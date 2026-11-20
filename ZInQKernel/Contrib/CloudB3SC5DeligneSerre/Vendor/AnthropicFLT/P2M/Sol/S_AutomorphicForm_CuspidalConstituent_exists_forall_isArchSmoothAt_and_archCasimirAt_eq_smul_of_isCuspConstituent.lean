/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent (git blob 323ffdfbd958ad44dd437e45ae9ace629621674a, sha256 06c744e16f1b4d8f3cb14c9b62e40e01619c3af4f34334f9cf9fe1823e22e94d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_forall_isReal
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_exists_isComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent

set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
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
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (w : InfinitePlace K) (hw : w.IsReal) :
    ∃ lam : ℂ, ∀ x ∈ V, IsArchSmoothAt hw x ∧ (∀ d : ArchDir, Continuous (archDerivAt hw d x)) ∧
      (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) ∧ archCasimirAt hw x = lam • x := by
  by_cases hreal : ∀ v : InfinitePlace K, v.IsReal
  · exact AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_forall_isReal
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys hX hreal w hw
  · have hcx : ∃ v : InfinitePlace K, v.IsComplex := by
      push_neg at hreal
      obtain ⟨v, hv⟩ := hreal
      exact ⟨v, InfinitePlace.not_isReal_iff_isComplex.1 hv⟩
    exact AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent_of_exists_isComplex
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys hX hcx w hw
