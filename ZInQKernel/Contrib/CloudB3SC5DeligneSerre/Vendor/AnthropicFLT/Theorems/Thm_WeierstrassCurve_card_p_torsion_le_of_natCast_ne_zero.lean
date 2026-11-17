/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_card_p_torsion_le_of_natCast_ne_zero (git blob 4bb93b86ffc363c5dc32a9561706ac8f6801835d, sha256 9449b888792b5e9d124c90d02c567a384713284c1c134dca76e78de248a246e7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_card_p_torsion_le_of_natCast_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.card_p_torsion_le_of_natCast_ne_zero {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {p : ℕ} [W.IsElliptic] (hp : p.Prime) (hp5 : 5 ≤ p) (hpF : (p : F) ≠ 0) : Nat.card (Submodule.torsionBy ℤ W.toAffine.Point p) ≤ p ^ 2 := by
  revert F W p hp hp5 hpF
  exact @_root_.P2MW.S_WeierstrassCurve_card_p_torsion_le_of_natCast_ne_zero.solution
