/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet (git blob cb2fc3a7cef8679f5a6c1b0cd46c468fff51413c, sha256 abfbaa0ffeb6ff3bac19ec53c2426dd6d739e58ae0661824e757b1cc964b3d24).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SiegelCovering
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped NumberField
theorem AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
    (K : Type) [Field K] [NumberField K] :
    ∃ T : Finset (AutomorphicForm.AdelicGL2 (𝓞 K) K), ∃ c : ℝ, 0 < c ∧ ∃ u : ℝ,
      ∀ d₁ d₂ : ℝ, 0 < d₂ → d₁ ≤ d₂ →
        AutomorphicForm.SiegelCovering.CoversModCentre K
          (⋃ x ∈ T, (· * x) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet K c u d₁ d₂) := by
  revert K
  exact @_root_.P2MW.S_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet.solution
