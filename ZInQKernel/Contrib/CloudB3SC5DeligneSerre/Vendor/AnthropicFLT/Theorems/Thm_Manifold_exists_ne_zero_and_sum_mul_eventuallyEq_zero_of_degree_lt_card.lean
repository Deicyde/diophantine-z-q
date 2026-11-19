/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card (git blob 11747aec4c24297cdbaff8dff278e5c49bfae4bd, sha256 80fb004b12938cb2f6c3bfb650b059df053f5876f6cca410ab29d651be9c7f66).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped Manifold ContDiff Topology

theorem Manifold.exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    [CompactSpace M] [ConnectedSpace M]
    (D : M →₀ ℕ) {ι : Type*} [Fintype ι] (ψ : ι → M → ℂ)
    (hψ : ∀ i x, MeromorphicAt (fun z : ℂ => ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x))
    (hord : ∀ i x, ((-(D x : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z : ℂ => ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x))
    (hcard : (D.sum fun _ n => n) + 1 < Fintype.card ι) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ ∀ x : M, (fun z : ℂ => ∑ i, c i * ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x)] 0 := by
  revert M D ι ψ hψ hord hcard
  exact @_root_.P2MW.S_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card.solution
