/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_TateCurve_point_mul_eq_add_of_norm_eq_one (git blob 9806da4aa8148d5f62c705a3553ca0b599ca3eac, sha256 6079e5979fe0c49c3b43bbf3a3adfd2237bd2516b6d630c9b087b5297eb7b133).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_TateCurve_point_mul_eq_add_of_norm_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open TateCurve WeierstrassCurve.Affine
open scoped NNReal

universe u in

theorem TateCurve.point_mul_eq_add_of_norm_eq_one
    {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] [IsAlgClosed K]
    {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {v w : K} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v * w ≠ 1)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (v * w)) (pointY q (v * w)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q w) (pointY q w)) :
    (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃ := by
  revert K q hq0 hq v w hv hw hv1 hw1 hvw h₁ h₂ h₃
  exact @_root_.P2MW.S_TateCurve_point_mul_eq_add_of_norm_eq_one.solution
