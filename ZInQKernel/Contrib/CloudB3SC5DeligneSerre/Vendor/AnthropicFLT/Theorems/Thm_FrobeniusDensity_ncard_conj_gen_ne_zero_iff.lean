/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_ncard_conj_gen_ne_zero_iff (git blob 3e30f00ad415593b94aaf2cd745a5cb4daf61946, sha256 296b6b2519a4f7d2fed1bc816a3bc951967c0a9574ebce71a71d806169636b0d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Set.Card
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem FrobeniusDensity.ncard_conj_gen_ne_zero_iff {G : Type*} [Group G] [Finite G]
    (σ τ : G) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard ≠ 0
      ↔ ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) τ := by
  revert G σ τ
  exact @_root_.P2MW.S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff.solution
