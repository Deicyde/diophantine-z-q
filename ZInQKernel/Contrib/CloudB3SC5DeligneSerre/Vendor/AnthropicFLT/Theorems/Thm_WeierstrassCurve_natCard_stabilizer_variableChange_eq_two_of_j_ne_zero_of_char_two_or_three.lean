/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three (git blob a49939c6a13f169b3f909e80bcfa2baf189ef6f3, sha256 9d0027d45e6c41c650735104afa1f9b1202a1a417548c451a5b1134b7050f929).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
    {F : Type*} [Field F] (hF : ringChar F = 2 ∨ ringChar F = 3)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj0 : E.j ≠ 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 2 := by
  revert F hF E hj0
  exact @_root_.P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three.solution
