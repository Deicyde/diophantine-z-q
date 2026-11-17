/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one (git blob 49c6d1cc565187d0052aaca7f142b846150d664a, sha256 9171ab894c8d9698e60c0dc726fad9a86a577decc7b2793c1a06b8ba49c1a68b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one
    (a b : ℂ) (N : ℝ) (hN : 1 < N) (hb : ‖b‖ = 1) (hab : ∃ t : ℝ, 0 ≤ t ∧ a ^ 2 = (t : ℂ) * b)
    (ha : ‖a‖ ^ 2 < N + 2 + N⁻¹) :
    ∃ c : ℕ → ℝ, c 0 = 0 ∧ c 1 = ‖a‖ ^ 2 ∧ (∀ m : ℕ, 0 ≤ c m) ∧ (∀ m : ℕ, c m ≤ 4 * N ^ m) ∧
      ∀ y : ℂ, ‖y‖ < N⁻¹ →
        Summable (fun m : ℕ => (c m : ℂ) * y ^ m) ∧
        Complex.exp (∑' m : ℕ, (c m : ℂ) * y ^ m) = ((rsEulerPoly (a / b) b⁻¹ a b 0).eval y)⁻¹ := by
  revert a b N hN hb hab ha
  exact @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one.solution
