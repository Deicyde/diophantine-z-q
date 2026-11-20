/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth (git blob bf175b099fb20cd097acec0efca8bbcb83dfd47d, sha256 ec2a5fb3a1491e6a251d37867d722c8c43deec5e77f632a40cc7a093afd6472a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth
    (n m : ℕ) (k : ℝ) (ν : ℂ) (hk : k = n + 1 + 2 * m) (hν : ν = (n : ℂ) / 2) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ δ := by
  revert n m k ν hk hν f hf hf' hfeq hfgr
  exact @_root_.P2MW.S_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth.solution
