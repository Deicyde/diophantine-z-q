/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728 (git blob 755ae0d5552fbec79ded1f13db4747bd6b802c5e, sha256 0d7a317b7acbe254acb08a77122ec89275ecbd088a4ed7c0dd86a803520330b0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj0 : E.j ≠ 0) (hj1728 : E.j ≠ 1728) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 2 := by
  revert F h2 h3 E hj0 hj1728
  exact @_root_.P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728.solution
