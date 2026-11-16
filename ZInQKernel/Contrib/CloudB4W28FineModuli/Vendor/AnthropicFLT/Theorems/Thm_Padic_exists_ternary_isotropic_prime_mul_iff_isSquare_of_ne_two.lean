/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Apache License 2.0; see LICENSE, NOTICE.upstream and ATTRIBUTION.upstream.md.
W28 compatibility changes: relocated imports; removed imported-only global attribute
suppressions and unused P2M.Util; direct exact solution wrappers; upstream Lake options
made explicit below. Exact bridge cuts, when present, are recorded in SOURCE_MANIFEST.json.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.P2M.Sol.S_Padic_exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


theorem Padic.exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : ℚ_[p]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (∃ z x y : ℚ_[p], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (p * a) * x ^ 2 - b * y ^ 2 = 0) ↔ IsSquare b := by apply @_root_.P2MW.S_Padic_exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two.solution <;> assumption
