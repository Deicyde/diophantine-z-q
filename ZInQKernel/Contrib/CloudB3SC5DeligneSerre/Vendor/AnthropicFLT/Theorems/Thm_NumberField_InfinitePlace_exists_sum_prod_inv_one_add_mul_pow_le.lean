/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_InfinitePlace_exists_sum_prod_inv_one_add_mul_pow_le (git blob 889f356c4ca8d3e9cfca18bb900f45aaf43cf442, sha256 054c7995e5a1509f30b02e20e49b6ba1fad4a0fed5f6176a1642434960286b9f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_InfinitePlace_exists_sum_prod_inv_one_add_mul_pow_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem NumberField.InfinitePlace.exists_sum_prod_inv_one_add_mul_pow_le
    (F : Type) [Field F] [NumberField F] {s : NumberField.RingOfIntegers F} (hs : s ≠ 0) (N : ℕ) :
    ∃ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : NumberField.InfinitePlace F → ℝ, (∀ w, 0 < y w) →
      1 ≤ ∏ w, y w ^ w.mult →
      ∀ T : Finset F,
        (∀ ξ ∈ T, ξ ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers F, (a : F) = (s : F) * ξ) →
        ∑ ξ ∈ T, ∏ w : NumberField.InfinitePlace F, ((1 + y w * w ξ) ^ M)⁻¹
          ≤ C * ((∏ w : NumberField.InfinitePlace F, y w ^ w.mult) ^ N)⁻¹ := by
  revert F s hs N
  exact @_root_.P2MW.S_NumberField_InfinitePlace_exists_sum_prod_inv_one_add_mul_pow_le.solution
