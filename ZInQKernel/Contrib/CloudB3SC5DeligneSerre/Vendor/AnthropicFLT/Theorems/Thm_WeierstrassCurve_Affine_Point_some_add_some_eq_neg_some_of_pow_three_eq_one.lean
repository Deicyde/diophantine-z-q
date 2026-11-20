/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_Affine_Point_some_add_some_eq_neg_some_of_pow_three_eq_one (git blob f03aea091017df66cfc07dde952e497a7fdaabf7, sha256 4bc1925930d3d5c72dfba656bbef3228f96b6161bd72e36df40ea8391b2b772c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_Affine_Point_some_add_some_eq_neg_some_of_pow_three_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem WeierstrassCurve.Affine.Point.some_add_some_eq_neg_some_of_pow_three_eq_one
    {k : Type*} [Field k] [DecidableEq k] (B w : k) (hw : w ^ 3 = 1) (hw1 : w ≠ 1) {x y : k}
    (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular x y)
    (hwx : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular (w * x) y)
    (hw2x : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular (w ^ 2 * x) y) (hx : x ≠ 0) :
    (WeierstrassCurve.Affine.Point.some x y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some (w * x) y hwx
      = -(WeierstrassCurve.Affine.Point.some (w ^ 2 * x) y hw2x) := by
  revert k B w hw hw1 x y h hwx hw2x hx
  exact @_root_.P2MW.S_WeierstrassCurve_Affine_Point_some_add_some_eq_neg_some_of_pow_three_eq_one.solution
