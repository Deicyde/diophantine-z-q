/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_mul_pow_inv_mem_of_finiteDimensional_adjoin (git blob 3626e58e01367fc874f0ff99f38f82e8f2766df8, sha256 2ae4e0975416aebe32bd35b77aa92966554da7490b17decbff8996ffa6a64214).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_mul_pow_inv_mem_of_finiteDimensional_adjoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.exists_mul_pow_inv_mem_of_finiteDimensional_adjoin
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (f : F) [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (u : F)
    (h₁ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) :
    ∃ m : ℕ, ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∉ V →
      u * (f ^ m)⁻¹ ∈ V := by
  revert L F f u h₁
  exact @_root_.P2MW.S_ValuationSubring_exists_mul_pow_inv_mem_of_finiteDimensional_adjoin.solution
