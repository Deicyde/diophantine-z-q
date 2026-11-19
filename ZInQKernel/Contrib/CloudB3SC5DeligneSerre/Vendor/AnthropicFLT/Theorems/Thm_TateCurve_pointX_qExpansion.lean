/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_TateCurve_pointX_qExpansion (git blob f3ac5682ad96f973f4296f991e1e5763da714984, sha256 9165e4df4b1c52eff925225a8575734e279b1d9905944d106ae889bb4d51099a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_Tails
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_TateCurve_pointX_qExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open TateCurve
open scoped NNReal
theorem TateCurve.pointX_qExpansion {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) : pointX q u = xfun u + ∑' N : ℕ, xCoeff u (N + 1) * q ^ (N + 1) := by
  revert K q u hq0 hq hu0 hu hqu hqu'
  exact @_root_.P2MW.S_TateCurve_pointX_qExpansion.solution
