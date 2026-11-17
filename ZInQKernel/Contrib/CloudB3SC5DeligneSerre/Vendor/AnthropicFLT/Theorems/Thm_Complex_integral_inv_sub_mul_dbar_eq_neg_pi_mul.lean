/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul (git blob d6e72f05f62a7b2930a863155d44fa62157f712f, sha256 e899afcd0ccec77049f833b1d1683c7fcbcff6e07c179b38e7cfd5be8e9744b7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Complex MeasureTheory
open scoped Real

theorem Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul
    (a : ℂ) (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) :
    ∫ z, (z - a)⁻¹ * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * h a := by
  revert a h hh hsupp
  exact @_root_.P2MW.S_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul.solution
