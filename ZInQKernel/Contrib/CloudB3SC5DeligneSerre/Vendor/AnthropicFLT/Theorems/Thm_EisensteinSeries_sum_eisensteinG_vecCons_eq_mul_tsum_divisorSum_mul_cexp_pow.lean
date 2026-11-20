/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinSeries_sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow (git blob 8b9b03533a6d41db3a739797e7550be3d9a8f6c0, sha256 01ff02ce69bece63603911b502395c916f1a338020752648fba52227f4f6777b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EisensteinSeries_EisensteinG
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinSeries_sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped Real in

theorem EisensteinSeries.sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow
    (N : ℕ) [NeZero N] (a : ZMod N) (ha : a ≠ 0) {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : UpperHalfPlane) :
    ∑ e : ZMod N, EisensteinSeries.eisensteinG N k ![a, e] z =
      ((-2 * π * Complex.I) ^ k / (Nat.factorial (k - 1) : ℂ)) *
        ∑' n : ℕ, (∑ d ∈ n.divisors,
            ((if ((n / d : ℕ) : ZMod N) = a then (d : ℂ) ^ (k - 1) else 0) +
              (if ((n / d : ℕ) : ZMod N) = -a then (d : ℂ) ^ (k - 1) else 0))) *
          Complex.exp (2 * π * Complex.I * z) ^ n := by
  revert N a ha k hk hk2 z
  exact @_root_.P2MW.S_EisensteinSeries_sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow.solution
