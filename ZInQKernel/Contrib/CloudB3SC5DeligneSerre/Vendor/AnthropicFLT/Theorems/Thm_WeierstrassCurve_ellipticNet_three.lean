/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_ellipticNet_three (git blob 4e82be295d0f42705481e56c13515aaf6b7e8716, sha256 5dbd573de83be9d596cefb836824b70fe3ccf69b0b04b23d468054ed4cadeb3e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_ellipticNet_three
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_DivPolyMulFormula

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Polynomial
theorem P2M.Dup.WeierstrassCurve.ellipticNet_three {R : Type*} [CommRing R] (W : WeierstrassCurve R) (t : R) :
    2 * t * (W.Φ 3).eval t * ((W.Φ 3).eval t + t * (W.ΨSq 3).eval t) +
        W.b₂ * t * ((W.Φ 3).eval t * (W.ΨSq 3).eval t) +
        W.b₄ * (((W.Φ 3).eval t + t * (W.ΨSq 3).eval t) * (W.ΨSq 3).eval t) +
        W.b₆ * (W.ΨSq 3).eval t ^ 2 =
      (W.Φ 4).eval t * (W.ΨSq 2).eval t + (W.Φ 2).eval t * (W.ΨSq 4).eval t := by
  revert R W t
  exact @_root_.P2MW.S_WeierstrassCurve_ellipticNet_three.solution

