/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Function_exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul (git blob 02376ca221b1a5a7859e0e7015a1c5aa72d8c004, sha256 e27957b44e8957e8490eebcd0683b5113282b59c605ecc7bf80d8d5c5328cc5b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Function_exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Function.exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul
    {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Φ : (∀ i, X i) → ℂ) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → ∃ (d : ℕ) (φ : Fin d → X i → ℂ), ∀ b : ∀ j, X j, ∃ c : Fin d → ℂ,
      ∀ t : X i, Φ (Function.update b i t) = ∑ k, c k * φ k t) :
    ∃ (m : ℕ) (coef : Fin m → ℂ) (β : Fin m → ι → ∀ j, X j),
      ∀ t : ∀ j, X j, Φ t = ∑ α, coef α * ∏ i, Φ (Function.update (β α i) i (t i)) := by
  revert ι X Φ i₀ h
  exact @_root_.P2MW.S_Function_exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul.solution
