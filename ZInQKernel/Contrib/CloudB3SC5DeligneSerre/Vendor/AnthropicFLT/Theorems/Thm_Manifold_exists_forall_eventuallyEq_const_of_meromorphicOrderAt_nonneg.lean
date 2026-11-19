/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg (git blob 4d98408899a2cba2a8ab84af3e433c5497241ff5, sha256 36fe4b515f63986317087b844f7aa5b49f5d43e1cde065523fcbb0f408831d83).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped Manifold ContDiff Topology

theorem Manifold.exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    [CompactSpace M] [ConnectedSpace M]
    (g : M → ℂ)
    (hg : ∀ x : M, MeromorphicAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x))
    (hg0 : ∀ x : M, 0 ≤ meromorphicOrderAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x)) :
    ∃ C : ℂ, ∀ x : M, (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x)] fun _ => C := by
  revert M g hg hg0
  exact @_root_.P2MW.S_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg.solution
