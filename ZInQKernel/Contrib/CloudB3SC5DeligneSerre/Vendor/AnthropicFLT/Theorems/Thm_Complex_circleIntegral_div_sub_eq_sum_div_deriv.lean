/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_circleIntegral_div_sub_eq_sum_div_deriv (git blob a4a23eeae2260b97965169467ef62d2885f97ab1, sha256 aca1e7094b002defc8daa5cb746f3fb2aeaadd9ce11d50ef456abaa55c73072c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_circleIntegral_div_sub_eq_sum_div_deriv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Complex.circleIntegral_div_sub_eq_sum_div_deriv {R Ψ : ℂ → ℂ} {c t : ℂ} {r : ℝ}
    (hr : 0 < r) (hR : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ R z)
    (hΨ : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ Ψ z)
    (hne : ∀ z ∈ Metric.sphere c r, R z ≠ t) (Z : Finset ℂ)
    (hZ : ∀ a, a ∈ Z ↔ a ∈ Metric.ball c r ∧ R a = t) (hsimple : ∀ a ∈ Z, deriv R a ≠ 0) :
    (∮ z in C(c, r), Ψ z / (R z - t)) =
      2 * Real.pi * Complex.I * ∑ a ∈ Z, Ψ a / deriv R a := by
  revert R Ψ c t r hr hR hΨ hne Z hZ hsimple
  exact @_root_.P2MW.S_Complex_circleIntegral_div_sub_eq_sum_div_deriv.solution
