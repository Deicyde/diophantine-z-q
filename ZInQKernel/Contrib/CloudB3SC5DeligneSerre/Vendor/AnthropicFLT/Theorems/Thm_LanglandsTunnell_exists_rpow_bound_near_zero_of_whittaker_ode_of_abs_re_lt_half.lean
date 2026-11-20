/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half (git blob 184638e904b3393a096b3c5f65236dadb360fbf2, sha256 b4a04b076ae354eb308ea0e9529e6830aa38330ab422477b9eac3763b6da3e13).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half
    (ν : ℂ) (hre : |ν.re| < 1 / 2) (k : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ δ := by
  revert ν hre k f hf hf' hfeq
  exact @_root_.P2MW.S_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half.solution
