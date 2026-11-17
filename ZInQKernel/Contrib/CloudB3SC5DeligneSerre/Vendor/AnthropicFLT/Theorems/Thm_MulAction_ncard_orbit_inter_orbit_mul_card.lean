/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MulAction_ncard_orbit_inter_orbit_mul_card (git blob 055f0f4392946a77d9153ff60e7e42baed4a789f, sha256 c1691f6b5ed5ea0469a1e5b24e8c0b056fcd775be38adf8cd97012ad3db89a75).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.GroupTheory.Index
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MulAction_ncard_orbit_inter_orbit_mul_card

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem MulAction.ncard_orbit_inter_orbit_mul_card {G : Type*} [Group G] {X : Type*} [MulAction G X] [Finite G] [MulAction.IsPretransitive G X] (H₁ H₂ : Subgroup G) (hprod : ∀ g : G, ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂) (x₁ x₂ : X) : (MulAction.orbit H₁ x₁ ∩ MulAction.orbit H₂ x₂).ncard * Nat.card X = (MulAction.orbit H₁ x₁).ncard * (MulAction.orbit H₂ x₂).ncard := by
  revert G X H₁ H₂ hprod x₁ x₂
  exact @_root_.P2MW.S_MulAction_ncard_orbit_inter_orbit_mul_card.solution
