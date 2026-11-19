/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff (git blob 8c28fe9d7b96d256c47d841e3e244e68452f2851, sha256 375b96868f786fbedcb104cbb731cc63c379fbf4edcd9290b36259b0e0e52064).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 := by
  revert F W x y h n
  exact @_root_.P2MW.S_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff.solution
