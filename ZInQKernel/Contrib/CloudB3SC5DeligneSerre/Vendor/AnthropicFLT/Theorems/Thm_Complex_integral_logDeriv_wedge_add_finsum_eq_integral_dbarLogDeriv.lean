/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv (git blob 4980196d8c1833a4053b737baa225d9f1c009d03, sha256 a9d13ef2d2d21158d019ba7088b157731adeb206d171812769635d438fc02b9e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Complex MeasureTheory
open scoped Real Topology

theorem Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv
    (U : Set ℂ) (hU : IsOpen U) (Φ : ℂ → ℂ) (n : ℂ → ℤ)
    (hloc : ∀ τ ∈ U, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 τ] fun z => (z - τ) ^ (n τ) * Ψ z)
    (E E' : ℂ → ℂ) (hE : ∀ z ∈ U, HasDerivAt E (E' z) z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 2 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    Integrable (fun z : ℂ => E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) ∧
    Integrable (fun z : ℂ => E' z * h z *
        ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) ∧
    I / π * (∫ z : ℂ, E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) +
      2 * ∑ᶠ a : ℂ, (n a : ℂ) * E a * h a =
    2 / π * ∫ z : ℂ, E' z * h z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) := by
  revert U hU Φ n hloc E E' hE h hh hsupp hU'
  exact @_root_.P2MW.S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv.solution
