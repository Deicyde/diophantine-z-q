/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum (git blob 204a70555ccc6c3af49fb225ea774d798acb6107, sha256 bf4ef2e661886698acd8435395c01ea0f1a28a4767865f15044e5b5c0aebd936).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open MeasureTheory Complex
open scoped Topology Real

theorem Complex.integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum
    (U : Set ℂ) (hU : IsOpen U) (F : ℂ → ℂ) (hF : ∀ z ∈ U, MeromorphicAt F z)
    (hF' : ∀ z ∈ U, meromorphicOrderAt F z ≠ ⊤)
    (E : ℂ → ℂ) (hE : DifferentiableOn ℂ E U)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, E z * (deriv F z / F z) * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) =
      -π * ∑ᶠ a, (((meromorphicOrderAt F a).untop₀ : ℤ) : ℂ) * E a * h a := by
  revert U hU F hF hF' E hE h hh hsupp hU'
  exact @_root_.P2MW.S_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum.solution
