/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun (git blob d252c2c2f6558215824cf3b9d83c9bb418d767e8, sha256 81be0419490986d28c8d9d4561e5185485b8004248863a9579eb08ad2261e5c3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Real Complex
open scoped Nat

theorem ZMod.tsum_intCast_pow_inv_eq_sum_bernoulliFun (N : ℕ) [NeZero N] (k : ℕ) (hk : 2 ≤ k)
    (a : ZMod N) :
    ∑' d : {d : ℤ // (d : ZMod N) = a}, ((d : ℂ) ^ k)⁻¹ =
      -(2 * π * I) ^ k / (k ! * N) *
        ∑ r : ZMod N, ZMod.stdAddChar (-(r * a)) * (bernoulliFun k ((r.val : ℝ) / N) : ℂ) := by
  revert N k hk a
  exact @_root_.P2MW.S_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun.solution
