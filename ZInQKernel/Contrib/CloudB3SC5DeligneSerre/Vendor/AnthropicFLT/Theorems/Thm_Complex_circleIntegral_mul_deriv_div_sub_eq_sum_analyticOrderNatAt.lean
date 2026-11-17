/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt (git blob 6f2fdc3c63bb6d90fb384a3011ced32fdab9fffd, sha256 3fedcddb03bc5747da4f1583f2e07ca39cdefd605f9920b47e9e438667f853e8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped Real

theorem Complex.circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt
    {R G : ℂ → ℂ} {z₀ t : ℂ} {r : ℝ} (hr : 0 < r)
    (hR : ∀ z ∈ Metric.closedBall z₀ r, AnalyticAt ℂ R z)
    (hG : ∀ z ∈ Metric.closedBall z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ Metric.sphere z₀ r, R z ≠ t) :
    ∃ Z : Finset ℂ, (∀ a, a ∈ Z ↔ a ∈ Metric.ball z₀ r ∧ R a = t) ∧
      (∮ z in C(z₀, r), G z * deriv R z / (R z - t)) =
        2 * π * Complex.I *
          ∑ a ∈ Z, (analyticOrderNatAt (fun z => R z - t) a : ℂ) * G a := by
  revert R G z₀ t r hr hR hG hne
  exact @_root_.P2MW.S_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt.solution
