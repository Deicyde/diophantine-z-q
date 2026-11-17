/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinSeries_tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral (git blob a84956b0238147de43e05883854298c93dc74081, sha256 feb090a16e2c23416b7cc9e2db8ee5cd00b0ed8ad0a8d8aafab0128babda148e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinSeries_tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem EisensteinSeries.tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral
    (N : ℕ) (hN : 3 ≤ N) :
    (∑' d : {d : ℤ // (d : ZMod N) = 1}, ((d : ℂ) ^ 3)⁻¹) ≠ 0 ∧
    ∃ a : ℕ,
      IsIntegral ℤ ((N : ℂ) ^ a * (2 / (2 * Real.pi * Complex.I) ^ 3 *
        ∑' d : {d : ℤ // (d : ZMod N) = 1}, ((d : ℂ) ^ 3)⁻¹)) ∧
      IsIntegral ℤ ((N : ℂ) ^ a * (2 / (2 * Real.pi * Complex.I) ^ 3 *
        ∑' d : {d : ℤ // (d : ZMod N) = 1}, ((d : ℂ) ^ 3)⁻¹)⁻¹) := by
  revert N hN
  exact @_root_.P2MW.S_EisensteinSeries_tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral.solution
