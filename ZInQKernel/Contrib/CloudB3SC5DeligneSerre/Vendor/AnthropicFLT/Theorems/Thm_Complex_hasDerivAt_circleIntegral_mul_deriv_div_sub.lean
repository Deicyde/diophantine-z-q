/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub (git blob de3ec9ee618d4f7cddae1d7c8cf1d4a2b5360bf7, sha256 12d1255cca4aca82765b2717eb905ea8b843cbb3d5de375d65178dfb2e153ea1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped Real

theorem Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub
    {Φ G : ℂ → ℂ} {z₀ t₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hΦ : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ Φ z)
    (hG : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ Metric.sphere z₀ r, Φ z ≠ t₀) :
    HasDerivAt (fun t : ℂ => ∮ z in C(z₀, r), G z * deriv Φ z / (Φ z - t))
      (∮ z in C(z₀, r), deriv G z / (Φ z - t₀)) t₀ := by
  revert Φ G z₀ t₀ r hr hΦ hG hne
  exact @_root_.P2MW.S_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub.solution
