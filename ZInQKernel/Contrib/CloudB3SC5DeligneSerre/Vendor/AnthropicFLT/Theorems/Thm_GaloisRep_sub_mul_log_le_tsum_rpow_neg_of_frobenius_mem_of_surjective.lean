/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_GaloisRep_sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective (git blob 12da50b60d052e6a21438576f5ce8343dfaadb7c, sha256 1a35c8c10e3186ab839aacc5ddfbfe74f9c340e39a21af9848881491a6ba341e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Residual
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_GaloisRep_sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false



theorem GaloisRep.sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective
    {Q : Type} [Group Q] [Finite Q] (π : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Q) (hπ : Function.Surjective π)
    (hπc : GaloisFactorsThroughFiniteLevel π)
    (C : Set Q) (hC : ∀ g h : Q, g ∈ C → h * g * h⁻¹ ∈ C)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      ((Nat.card C : ℝ) / Nat.card Q - δ) * Real.log (1 / (s - 1)) ≤
        ∑' p : {p : ℕ // p.Prime ∧
            (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
              ∀ σ ∈ A.inertiaSubgroupIn ℚ, π σ = 1) ∧
            ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p ∧
              ∃ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p ∧ π σ ∈ C},
          ((p : ℕ) : ℝ) ^ (-s) := by
  revert Q π hπ hπc C hC δ hδ
  exact @_root_.P2MW.S_GaloisRep_sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective.solution
