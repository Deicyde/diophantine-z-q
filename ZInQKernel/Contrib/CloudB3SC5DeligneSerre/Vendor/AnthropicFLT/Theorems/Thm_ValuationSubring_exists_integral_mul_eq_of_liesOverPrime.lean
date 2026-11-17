/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime (git blob 1e563aefd3a6f5fe4038771e3418195a6ece3088, sha256 8d43cbd844a1fbef8e1eb915bc4bb43e11f0fceb7de537016143d777124dfbcb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Ramification
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.exists_integral_mul_eq_of_liesOverPrime (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) (a : AlgebraicClosure ℚ) (ha : a ∈ A) : ∃ x s : integralClosure ℤ (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) ∉ A.nonunits ∧ a * s = x := by
  revert A q hq hA a ha
  exact @_root_.P2MW.S_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime.solution
