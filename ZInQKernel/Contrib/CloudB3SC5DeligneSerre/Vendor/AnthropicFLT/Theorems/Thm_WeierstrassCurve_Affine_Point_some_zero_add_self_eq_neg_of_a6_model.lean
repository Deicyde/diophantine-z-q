/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model (git blob 2ecaace6812c8e8ae543d8763f9c68002071f071, sha256 8d803dc6d4e4712cef69cdb9e63951b743c50b2af0635982ec7472549ce149ad).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem WeierstrassCurve.Affine.Point.some_zero_add_self_eq_neg_of_a6_model
    {k : Type*} [Field k] [DecidableEq k] (B : k) (h2 : (2 : k) ≠ 0) {y : k} (hy0 : y ≠ 0)
    (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular 0 y) :
    (WeierstrassCurve.Affine.Point.some 0 y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some 0 y h
      = -(WeierstrassCurve.Affine.Point.some 0 y h) := by
  revert k B h2 y hy0 h
  exact @_root_.P2MW.S_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model.solution
