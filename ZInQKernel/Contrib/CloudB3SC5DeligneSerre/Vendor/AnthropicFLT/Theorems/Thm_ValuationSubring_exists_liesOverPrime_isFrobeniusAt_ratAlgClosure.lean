/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure (git blob 6a60a07449d91fbfa482fb4ccf1e6504ef61ceed, sha256 f58f9359047ef2799a5d2c1ddec62d919500b949064855ca13d0c5519e531478).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups
theorem ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
    (p : Nat.Primes) :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      A.LiesOverPrime (p : ℕ) ∧ A.IsFrobeniusAt σ (p : ℕ) := by
  revert p
  exact @_root_.P2MW.S_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure.solution
