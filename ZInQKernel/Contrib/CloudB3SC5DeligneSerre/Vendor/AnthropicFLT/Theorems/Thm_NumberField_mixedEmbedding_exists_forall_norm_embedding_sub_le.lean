/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_mixedEmbedding_exists_forall_norm_embedding_sub_le (git blob a9322c92f10e675ada6cda7ccbedf4eae36813da, sha256 ec3b368213489cb8bb0c17644723ff07f90a1c3d4f60031baaf6cf7929116dd3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_mixedEmbedding_exists_forall_norm_embedding_sub_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem NumberField.mixedEmbedding.exists_forall_norm_embedding_sub_le (K : Type*) [Field K]
    [NumberField K] : ∃ U : ℝ, ∀ ξ : NumberField.InfinitePlace K → ℂ,
      (∀ w : NumberField.InfinitePlace K, w.IsReal → (ξ w).im = 0) →
        ∃ b : NumberField.RingOfIntegers K, ∀ w : NumberField.InfinitePlace K,
          ‖w.embedding (b : K) - ξ w‖ ≤ U := by
  revert K
  exact @_root_.P2MW.S_NumberField_mixedEmbedding_exists_forall_norm_embedding_sub_le.solution
