/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ArithmeticFunction_sum_moebius_filter_dvd (git blob 6cc3493855737b5f5203691ab450037c21a1d650, sha256 4e21b792e84bfdf7a74892c2d30e73d6b7b9a709263b63970fa487c88bb3ec4c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ArithmeticFunction_sum_moebius_filter_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped ArithmeticFunction.Moebius
theorem ArithmeticFunction.sum_moebius_filter_dvd {n m : ℕ} (hn : n ≠ 0) (hm : m ∣ n) :
    ∑ f ∈ n.divisors, ArithmeticFunction.moebius (n / f) * (if m ∣ f then 1 else 0)
      = if m = n then 1 else 0 := by
  revert n m hn hm
  exact @_root_.P2MW.S_ArithmeticFunction_sum_moebius_filter_dvd.solution
