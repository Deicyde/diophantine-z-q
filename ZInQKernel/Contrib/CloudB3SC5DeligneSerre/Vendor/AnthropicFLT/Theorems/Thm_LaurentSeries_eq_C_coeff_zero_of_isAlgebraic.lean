/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic (git blob 26fe8dcc243c20ba6f173a27bbfca03cf18a4e1d, sha256 fbc2e7562d184eb5bb6dbb949a645b6103642e2839423990f878b4aaed39e0ca).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem LaurentSeries.eq_C_coeff_zero_of_isAlgebraic {K : Type*} [Field K] {x : LaurentSeries K} (hx : IsAlgebraic K x) : x = HahnSeries.C (x.coeff 0) := by
  revert K x hx
  exact @_root_.P2MW.S_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic.solution
