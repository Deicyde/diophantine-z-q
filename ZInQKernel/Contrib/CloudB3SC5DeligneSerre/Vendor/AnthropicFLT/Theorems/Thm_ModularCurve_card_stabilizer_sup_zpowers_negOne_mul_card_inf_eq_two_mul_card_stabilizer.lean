/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer (git blob cb6eea7d2116abf365f3302ec7606f87e6881f55, sha256 9f9f7a2d0967bbaaec11ccc6d737d1c5937ecce7ac23a5c9fcd9636b2e4438a0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer
    (Γ : Subgroup SL(2, ℤ)) (τ : UpperHalfPlane) :
    Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) *
        Nat.card (Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) =
      2 * Nat.card (MulAction.stabilizer Γ τ) := by
  revert Γ τ
  exact @_root_.P2MW.S_ModularCurve_card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer.solution
