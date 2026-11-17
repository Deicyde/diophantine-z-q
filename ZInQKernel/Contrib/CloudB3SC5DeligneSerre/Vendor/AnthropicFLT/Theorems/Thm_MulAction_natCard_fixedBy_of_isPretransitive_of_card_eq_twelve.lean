/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MulAction_natCard_fixedBy_of_isPretransitive_of_card_eq_twelve (git blob d5a014680a5e2c2db6f6bf9c72d38990738e1712, sha256 82f2e2ea6327b2f7894d9452f137085566c0390323f87bfb9a251b65cc9438a0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MulAction_natCard_fixedBy_of_isPretransitive_of_card_eq_twelve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem MulAction.natCard_fixedBy_of_isPretransitive_of_card_eq_twelve
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 12)
    (hG' : ∀ g : G, g ^ 2 = 1 ∨ g ^ 3 = 1)
    (X : Type*) [MulAction G X] [Nonempty X] [MulAction.IsPretransitive G X] :
    (Nat.card X = 1 ∨ Nat.card X = 3 ∨ Nat.card X = 4 ∨ Nat.card X = 6 ∨ Nat.card X = 12) ∧
    (∀ a : G, a ≠ 1 → a ^ 2 = 1 →
      (Nat.card X = 1 → Nat.card (MulAction.fixedBy X a) = 1) ∧
      (Nat.card X = 3 → Nat.card (MulAction.fixedBy X a) = 3) ∧
      (Nat.card X = 4 → Nat.card (MulAction.fixedBy X a) = 0) ∧
      (Nat.card X = 6 → Nat.card (MulAction.fixedBy X a) = 2) ∧
      (Nat.card X = 12 → Nat.card (MulAction.fixedBy X a) = 0)) ∧
    (∀ b : G, b ≠ 1 → b ^ 3 = 1 →
      (Nat.card X = 1 → Nat.card (MulAction.fixedBy X b) = 1) ∧
      (Nat.card X = 3 → Nat.card (MulAction.fixedBy X b) = 0) ∧
      (Nat.card X = 4 → Nat.card (MulAction.fixedBy X b) = 1) ∧
      (Nat.card X = 6 → Nat.card (MulAction.fixedBy X b) = 0) ∧
      (Nat.card X = 12 → Nat.card (MulAction.fixedBy X b) = 0)) := by
  revert G hG hG' X
  exact @_root_.P2MW.S_MulAction_natCard_fixedBy_of_isPretransitive_of_card_eq_twelve.solution
