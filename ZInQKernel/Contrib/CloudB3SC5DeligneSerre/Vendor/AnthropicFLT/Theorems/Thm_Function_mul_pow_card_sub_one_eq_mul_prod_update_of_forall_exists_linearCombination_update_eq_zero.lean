/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Function_mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero (git blob 4eb89a0f6db116cd88b44af398048d598836ebd9, sha256 0edee53e89ac2327d279a4b4f0aa6393ed39c4fa6e63acc15e81cd40129f50fb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Function_mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Function.mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero
    {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Φ : (∀ i, X i) → ℂ) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → ∀ b b' : ∀ j, X j,
      ∃ c : ℂ × ℂ, c ≠ 0 ∧ ∀ t : X i, c.1 * Φ (Function.update b i t) + c.2 * Φ (Function.update b' i t) = 0)
    (b₀ t : ∀ j, X j) :
    Φ t * Φ b₀ ^ (Fintype.card ι - 1) =
      Φ (Function.update b₀ i₀ (t i₀)) * ∏ i ∈ Finset.univ.erase i₀, Φ (Function.update b₀ i (t i)) := by
  revert ι X Φ i₀ h b₀ t
  exact @_root_.P2MW.S_Function_mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero.solution
