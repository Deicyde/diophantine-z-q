/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex (git blob b4e979236c7a50c13728891ab489e792193fc352, sha256 ac90865bc3ac2fae7f1d3daff939b78b413e5e9a1c9a7bb9b56d34ab794d561c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem PowerSeries.exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex
    (φ : PowerSeries ℂ) (hφ : IsAlgebraic (Polynomial ℂ) φ) :
    ∃ C R : ℝ, ∀ n : ℕ, ‖PowerSeries.coeff n φ‖ ≤ C * R ^ n := by
  revert φ hφ
  exact @_root_.P2MW.S_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex.solution
