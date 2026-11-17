/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori (git blob d39174300db80ac9ed931618e676f623ff3793f7, sha256 323368826612d29fbc3a7042380833889d3df263769aa90899ecf61e26822e57).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori
    (ν : ℂ) (hν : 0 ≤ ν.re) (σ A r B : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hapriori : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ B * y ^ r)
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖(y : ℂ) * deriv f y - (1 / 2 - ν) * f y‖ ≤ C * y ^ (min (min (1 / 2 + ν.re) σ) (r + 2) - ε)) ∧
    (1 / 2 - ν.re < r → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖f y‖ ≤ C * y ^ (min (1 / 2 + ν.re) σ - ε) ∧
      ‖(y : ℂ) * deriv f y‖ ≤ C * y ^ (min (1 / 2 + ν.re) σ - ε)) := by
  revert ν hν σ A r B f h hf hf' hh hapriori hfeq
  exact @_root_.P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori.solution
