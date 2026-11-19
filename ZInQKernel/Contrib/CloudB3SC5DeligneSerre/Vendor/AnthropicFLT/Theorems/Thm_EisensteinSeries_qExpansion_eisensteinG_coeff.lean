/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinSeries_qExpansion_eisensteinG_coeff (git blob 5252b46e8a74c817890548dd2b021275c060635f, sha256 747164b3188f6d7e5650f47eea2389a3b9794d25bcdb80ea671efda57a07817e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EisensteinSeries_EisensteinG
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinSeries_qExpansion_eisensteinG_coeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Real Complex
open scoped Nat

theorem EisensteinSeries.qExpansion_eisensteinG_coeff (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N) (n : ℕ) :
    (UpperHalfPlane.qExpansion N (EisensteinSeries.eisensteinG N k a)).coeff n =
      if n = 0 then
        (if a 0 = 0 then ∑' d : {d : ℤ // (d : ZMod N) = a 1}, ((d : ℂ) ^ k)⁻¹ else 0)
      else
        (-2 * π * I) ^ k / ((k - 1)! * (N : ℂ) ^ k) *
          ∑ m ∈ n.divisors,
            ((if ((n / m : ℕ) : ZMod N) = a 0 then ZMod.stdAddChar (a 1 * (m : ZMod N)) else 0) +
              (-1) ^ k *
                (if ((n / m : ℕ) : ZMod N) = -a 0 then ZMod.stdAddChar (-(a 1 * (m : ZMod N))) else 0)) *
            (m : ℂ) ^ (k - 1) := by
  revert N k hk a n
  exact @_root_.P2MW.S_EisensteinSeries_qExpansion_eisensteinG_coeff.solution
