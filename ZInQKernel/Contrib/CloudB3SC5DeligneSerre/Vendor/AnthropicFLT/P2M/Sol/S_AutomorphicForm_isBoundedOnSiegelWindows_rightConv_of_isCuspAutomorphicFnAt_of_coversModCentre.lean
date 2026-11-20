/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre (git blob 2c40ae48f7a8e1d6fe9820855ac4b111f1083ff2, sha256 c3ef5186fdcb84823580a97ce8cbf6694a187dc212b92ab26004ed598d5d45f3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : IsFactorizableTestFn K f) :
    IsBoundedOnSiegelWindows K (rightConv K φ f) := by
  intro c' u' d₁' d₂' T' hc' hd₁'

  have key : ∀ t : AdelicGL2 (𝓞 K) K, ∃ C : ℝ, ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      ‖rightConv K φ f (s * t)‖ ≤ C := by
    intro t
    obtain ⟨Ccap, C₁, hhigh⟩ :=
      exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre K c u d₁ d₂ T hd
        hcov χ φ hφ hcont f hf c' u' d₁' d₂' t hc' hd₁'
    have hcpt : IsCompact (centreCutSiegelSet K c' u' d₁' d₂' ∩
        {g | ∀ w : InfinitePlace K, localHeight (archComponent K w (glArch (𝓞 K) K g)) ≤ Ccap}) :=
      isCompact_centreCutSiegelSet_inter_heightCap K hc' hd₁'
    have hcont' : Continuous (rightConv K φ f) :=
      (continuous_rightConv_and_contDiff_of_isFactorizableTestFn K φ hcont f hf).1
    have hmul : Continuous fun a : AdelicGL2 (𝓞 K) K => a * t := continuous_id.mul continuous_const
    obtain ⟨C₂, hC₂⟩ := (hcpt.image hmul).exists_bound_of_continuousOn hcont'.continuousOn
    refine ⟨max C₁ C₂, fun s hs => ?_⟩
    by_cases hcap : ∀ w : InfinitePlace K, localHeight (archComponent K w (glArch (𝓞 K) K s)) ≤ Ccap
    · exact (hC₂ (s * t) ⟨s, ⟨hs, hcap⟩, rfl⟩).trans (le_max_right _ _)
    · simp only [not_forall, not_le] at hcap
      exact (hhigh s hs hcap).trans (le_max_left _ _)
  choose Cof hCof using key
  refine ⟨∑ t ∈ T', max (Cof t) 0, fun g hg => ?_⟩
  obtain ⟨t, ht, hg'⟩ := Set.mem_iUnion₂.mp hg
  obtain ⟨s, hs, rfl⟩ := hg'
  calc ‖rightConv K φ f (s * t)‖ ≤ Cof t := hCof t s hs
    _ ≤ max (Cof t) 0 := le_max_left _ _
    _ ≤ ∑ t ∈ T', max (Cof t) 0 :=
        Finset.single_le_sum (f := fun t => max (Cof t) 0) (fun i _ => le_max_right _ _) ht
