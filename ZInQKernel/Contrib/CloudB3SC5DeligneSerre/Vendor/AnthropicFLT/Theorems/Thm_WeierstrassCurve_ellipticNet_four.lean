/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_ellipticNet_four (git blob cfc9262a13dafdaeab7435b2ae8d803fc5a9f439, sha256 7354e9e3e7c0b4755bfe7b5dae118467158ed61140350b00c18cc82483d212c9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_ellipticNet_four
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_DivPolyMulFormula

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Polynomial
theorem P2M.Dup.WeierstrassCurve.ellipticNet_four {R : Type*} [CommRing R] (W : WeierstrassCurve R) (t : R) :
    2 * t * (W.Φ 4).eval t * ((W.Φ 4).eval t + t * (W.ΨSq 4).eval t) +
        W.b₂ * t * ((W.Φ 4).eval t * (W.ΨSq 4).eval t) +
        W.b₄ * (((W.Φ 4).eval t + t * (W.ΨSq 4).eval t) * (W.ΨSq 4).eval t) +
        W.b₆ * (W.ΨSq 4).eval t ^ 2 =
      (W.Φ 5).eval t * (W.ΨSq 3).eval t + (W.Φ 3).eval t * (W.ΨSq 5).eval t := by
  revert R W t
  exact @_root_.P2MW.S_WeierstrassCurve_ellipticNet_four.solution

