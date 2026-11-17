/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem (git blob 0cf6f75fc990d1d7b11cd75c3f54eb90fea641b8, sha256 b48874583811fdb5d7f8025ed9ac5fcb3ff9876e607d426e408f97daba396f56).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.NumberTheory.NumberField.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped NumberField Pointwise
theorem ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem
    (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) [Qt.IsMaximal] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓQ : (ℓ : 𝓞 (AlgebraicClosure ℚ)) ∈ Qt) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hstab : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x ∈ Qt ↔ x ∈ Qt)
    (hfrob : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x - x ^ ℓ ∈ Qt)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ∀ x : AlgebraicClosure ℚ,
      x ∈ A ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧ ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a) :
    A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ := by
  revert Qt ℓ hℓ hℓQ τ hstab hfrob A hA
  exact @_root_.P2MW.S_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem.solution
