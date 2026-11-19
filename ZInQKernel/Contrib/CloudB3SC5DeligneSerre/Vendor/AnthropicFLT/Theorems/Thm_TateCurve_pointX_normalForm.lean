/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_TateCurve_pointX_normalForm (git blob 8bdd32e97d9db17bc15db3daf4e76dd959d39b27, sha256 ac3465177431c41dbe63142ddca968c58f9e18b34561003cfbe8ce4f4ddcf95c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_TateCurve_pointX_normalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open TateCurve
open scoped NNReal
theorem TateCurve.pointX_normalForm {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) : pointX q u = xfun u + ∑' n : ℕ, (xfun (q ^ (n + 1) * u) + xfun (q ^ (n + 1) * u⁻¹) - 2 * xfun (q ^ (n + 1))) := by
  revert K q u hq0 hq hu0 hu
  exact @_root_.P2MW.S_TateCurve_pointX_normalForm.solution
