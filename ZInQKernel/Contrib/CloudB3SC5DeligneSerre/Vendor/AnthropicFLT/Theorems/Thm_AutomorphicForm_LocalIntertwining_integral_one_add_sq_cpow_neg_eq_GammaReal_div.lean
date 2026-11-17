/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div (git blob 6761ffdbcf9dad29b0499e9eb795ec4b1ec73e73, sha256 6a2d40025d4aaef8ccb76752a78c293599ae73f7be5202cf4959373c5db81499).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div
    (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = Complex.Gammaℝ (2 * s) / Complex.Gammaℝ (2 * s + 1) := by
  revert s hs
  exact @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div.solution
