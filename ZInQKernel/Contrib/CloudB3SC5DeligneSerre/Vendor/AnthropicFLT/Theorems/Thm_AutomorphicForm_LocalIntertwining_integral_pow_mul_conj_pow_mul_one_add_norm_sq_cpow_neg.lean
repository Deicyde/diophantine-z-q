/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg (git blob 709b449db3dd6f228c698b51e8a9d729057c08f2, sha256 9cdcce8bea09ff550da05215a1f433e1b2672fefd212f716312cb1102bf399c7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem AutomorphicForm.LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg
    (a b : ℕ) (t : ℂ) (ht : ((a : ℝ) + b) / 2 + 1 < t.re) :
    ∫ z : ℂ, z ^ a * (starRingEnd ℂ z) ^ b * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-t)
      = if a = b then (Real.pi : ℂ) * (a.factorial : ℂ) * Complex.Gamma (t - 1 - a) / Complex.Gamma t
        else 0 := by
  revert a b t ht
  exact @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg.solution
