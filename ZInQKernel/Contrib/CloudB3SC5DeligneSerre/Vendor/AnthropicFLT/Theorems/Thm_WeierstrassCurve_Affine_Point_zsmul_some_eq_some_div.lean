/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div (git blob b594f281671193b35e47d7f78251c0c174deffb6, sha256 be92483a2f52c469468e3f43895b8f0e849810f21dc21766a66733dd3fb073fd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) : ∃ (y' : F) (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'), n • WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' := by
  revert F W x y h n hψ
  exact @_root_.P2MW.S_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div.solution
