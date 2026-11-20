/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg (git blob 7d3ddf7d588619986e99b13f04a11ed9b0c03b4a, sha256 0211fbd1567403828e954ef24c760c6ba9f30145eaeb3baa6c0cb9cede58df88).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField
open scoped Classical in

theorem NumberField.mixedEmbedding.exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg
    (F : Type) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (k N' : ℕ) (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ C : ℝ, ∀ t : ℝ, t₀ ≤ t →
      Summable (fun ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} =>
        (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k *
          (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ))) ∧
      ∑' ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I},
        (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k *
          (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ))
        ≤ C * t ^ (-(N' : ℝ)) := by
  revert F I k N' t₀ ht₀
  exact @_root_.P2MW.S_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg.solution
