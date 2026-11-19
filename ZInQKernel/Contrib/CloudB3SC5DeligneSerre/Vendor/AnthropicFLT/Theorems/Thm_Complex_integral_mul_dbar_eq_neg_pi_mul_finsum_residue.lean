/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue (git blob d98a528b60a92ce07ff3903ef4375c12e5325f7f, sha256 7812dc48f056d96c22262cc065c648b3e51f038231b00464f550716356fca1b1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Complex MeasureTheory
open scoped Topology Real

theorem Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue
    (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, F z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * ∑ᶠ a, c a * h a := by
  revert U hU F c hloc h hh hsupp hU'
  exact @_root_.P2MW.S_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue.solution
