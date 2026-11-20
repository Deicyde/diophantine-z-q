/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_TateCurve_pointY_inv (git blob d9d7fc66496cb28dcea7b03b475e14f4fb0a3012, sha256 31ca2cd5a84270835e66a0a9bc297ac0343ed4ad332a061188e5092d297a250d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_TateCurve_pointY_inv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open TateCurve
open scoped NNReal
theorem TateCurve.pointY_inv {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) : pointY q u⁻¹ = -pointY q u - pointX q u := by
  revert K q u hq0 hq hu0 hu
  exact @_root_.P2MW.S_TateCurve_pointY_inv.solution
