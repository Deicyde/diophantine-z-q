/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_SiegelUnit_exists_peaked_exponent (git blob 22be647aa9a2a284d55c2b14b446be053f0b4e0c, sha256 8b600019c0e2749ba4de6560c808693e4c0dd3671b1aa97eaa9c0f2a7031e00b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_SiegelUnit_exists_peaked_exponent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem ModularCurve.SiegelUnit.exists_peaked_exponent (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ∃ (m : ZMod N → ZMod N → ℕ) (Ord : ZMod N → ZMod N → ℤ),
      (∀ x y : ZMod N, Ord x y =
        ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
          (6 * (((r * x + s * y).val : ℕ) : ℤ) ^ 2
            - 6 * (N : ℤ) * (((r * x + s * y).val : ℕ) : ℤ) + (N : ℤ) ^ 2)) ∧
      m 0 0 = 0 ∧
      (∀ r s : ZMod N, m r (s + r) = m r s) ∧
      0 < Ord 1 0 ∧
      ∀ x y : ZMod N, (∃ a b : ZMod N, a * x + b * y = 1) →
        ¬ (y = 0 ∧ (x = 1 ∨ x = -1)) → ¬ (y = 1 ∨ y = -1) →
        Ord 1 0 < Ord x y := by
  revert N hN
  exact @_root_.P2MW.S_ModularCurve_SiegelUnit_exists_peaked_exponent.solution
