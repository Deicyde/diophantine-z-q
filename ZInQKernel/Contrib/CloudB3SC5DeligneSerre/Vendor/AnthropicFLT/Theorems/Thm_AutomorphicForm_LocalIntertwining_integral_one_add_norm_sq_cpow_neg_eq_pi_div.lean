/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_one_add_norm_sq_cpow_neg_eq_pi_div (git blob 0737c462d06b8c6338b19c4ab20851784354f16f, sha256 4f53fa6e391f1f8c06be6cff07e256bd3cafb49c6c51edcd88e6dbc555a4a3a9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_LocalIntertwining_integral_one_add_norm_sq_cpow_neg_eq_pi_div

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem AutomorphicForm.LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div
    (s : ℂ) (hs : 0 < s.re) :
    ∫ z : ℂ, ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)) = (Real.pi : ℂ) / (2 * s) := by
  revert s hs
  exact @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_integral_one_add_norm_sq_cpow_neg_eq_pi_div.solution
