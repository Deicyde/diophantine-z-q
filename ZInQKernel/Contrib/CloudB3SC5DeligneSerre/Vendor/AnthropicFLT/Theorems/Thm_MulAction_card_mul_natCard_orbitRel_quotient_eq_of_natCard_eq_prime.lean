/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MulAction_card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime (git blob bc5d79ab717d5b1331a93bf71c3829d648182a35, sha256 bf1337ea26832db77c603b57be20d2837d90c13eaa9a03f7d58135c39ccf0606).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MulAction_card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem MulAction.card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime
    (G : Type*) {X : Type*} [Group G] [MulAction G X] [Finite G] [Finite X]
    {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p) :
    p * Nat.card (MulAction.orbitRel.Quotient G X)
      = Nat.card X + (p - 1) * Nat.card (MulAction.fixedPoints G X) := by
  revert G X p hp hG
  exact @_root_.P2MW.S_MulAction_card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime.solution
