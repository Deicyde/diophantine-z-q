/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat (git blob 3207df1118e7b8499c97222ae994ba8383fb30fb, sha256 aad864a473ffff10ac49fa9465015a29a30517b26d9bf61e03a56f6ab11ca524).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Ramification
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.exists_liesOverPrime_algebraicClosure_rat (p : Nat.Primes) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) := by
  revert p
  exact @_root_.P2MW.S_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat.solution
