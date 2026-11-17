/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero (git blob 1d13992210b182a94f13cc82bdf9bf4c728c12a3, sha256 ce37da4ea58ba55a769d61015a6ff9c198b1213e28dba13ac51f66599b1cab5b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem ModularCurve.SiegelUnit.sum_totient_mul_levelBernoulliWeight_dilate_eq_zero (N : ℕ) [NeZero N]
    (s : ZMod N) (hs : s ≠ 0) :
    ∑ r : ZMod N,
        (((N / Nat.gcd r.val N) * Nat.totient (Nat.gcd r.val N) : ℕ) : ℤ) *
          (6 * (((s * r).val : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (((s * r).val : ℕ) : ℤ) + (N : ℤ) ^ 2) = 0 := by
  revert N s hs
  exact @_root_.P2MW.S_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero.solution
