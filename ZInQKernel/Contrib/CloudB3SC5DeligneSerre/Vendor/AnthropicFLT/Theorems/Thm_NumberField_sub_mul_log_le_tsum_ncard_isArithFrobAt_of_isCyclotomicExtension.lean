/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_sub_mul_log_le_tsum_ncard_isArithFrobAt_of_isCyclotomicExtension (git blob 5ca67d1bdab5ffca4fad6099c9858f329e820819, sha256 e003d71902d216983587d9d8d2af862d6c8b2686ad5ccfc33075278bd6422cf1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_sub_mul_log_le_tsum_ncard_isArithFrobAt_of_isCyclotomicExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField

theorem NumberField.sub_mul_log_le_tsum_ncard_isArithFrobAt_of_isCyclotomicExtension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (σ : L ≃ₐ[K] L) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      (1 / (orderOf σ : ℝ) - δ) * Real.log (1 / (s - 1)) ≤
        ∑' p : Nat.Primes, (({P : Ideal (𝓞 L) | P.IsMaximal ∧ ((p : ℕ) : 𝓞 L) ∈ P ∧
            IsArithFrobAt ℤ σ P}.ncard : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-s) := by
  revert K L m σ δ hδ
  exact @_root_.P2MW.S_NumberField_sub_mul_log_le_tsum_ncard_isArithFrobAt_of_isCyclotomicExtension.solution
