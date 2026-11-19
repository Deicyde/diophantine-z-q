/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat (git blob dbf75ee5a8d942246e1233c8d250d06fdb5f8cc0, sha256 70f47a986aed49018956f53d34ab7e038db89a15c4a4f39fb1731917bc4803d5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat

set_option autoImplicit false

theorem solution
    {p : ℕ} (hp : p.Prime) {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime p) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p :=
  ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hp A hA
