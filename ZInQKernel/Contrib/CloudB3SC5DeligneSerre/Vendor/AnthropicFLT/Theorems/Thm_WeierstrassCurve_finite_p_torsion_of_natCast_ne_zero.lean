/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_finite_p_torsion_of_natCast_ne_zero (git blob ce425caf2da7ac23f334e6c03a275f82bdfa2a5b, sha256 e02c987072e38feffe736c0862af215d8bab60312ebbd4dd47567500bd5d03e2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_finite_p_torsion_of_natCast_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.finite_p_torsion_of_natCast_ne_zero {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {p : ℕ} [W.IsElliptic] (hp : p.Prime) (hp5 : 5 ≤ p) (hpF : (p : F) ≠ 0) : Finite (Submodule.torsionBy ℤ W.toAffine.Point p) := by
  revert F W p hp hp5 hpF
  exact @_root_.P2MW.S_WeierstrassCurve_finite_p_torsion_of_natCast_ne_zero.solution
