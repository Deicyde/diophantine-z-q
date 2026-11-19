/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdeleRing_exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact (git blob 04aa7134f630ff4961725952686c14aacd8d2f67, sha256 f76ba22edd2eaa6fbfb4ff429de56b89d95c389ba68d19552727a81fecf99748).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdeleRing_exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped NumberField

theorem NumberField.AdeleRing.exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact
    (K : Type) [Field K] [NumberField K]
    {B : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)} (hB : IsCompact B) :
    ∃ M : ℝ, ∀ (a : NumberField.AdeleRing (𝓞 K) K) (R : NumberField.InfinitePlace K → ℝ),
      ∃ s : Finset K,
        (∀ k : K, (algebraMap K (NumberField.AdeleRing (𝓞 K) K) k - a).2 ∈ B →
          (∀ w : NumberField.InfinitePlace K,
            ‖(algebraMap K (NumberField.AdeleRing (𝓞 K) K) k - a).1 w‖ ≤ R w) → k ∈ s) ∧
        (s.card : ℝ) ≤ M * ∏ w : NumberField.InfinitePlace K, max 1 (R w) ^ w.mult := by
  revert K B hB
  exact @_root_.P2MW.S_NumberField_AdeleRing_exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact.solution
