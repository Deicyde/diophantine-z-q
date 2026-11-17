/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff (git blob 82d5ea46836f61c3af9094573c570bd250531fb0, sha256 6d95549627c8c60a1e0c26d07bd019ddd87627b5e964ddaa64cf690ba82fcb64).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Set.Card

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff

set_option autoImplicit false

theorem solution {G : Type*} [Group G] [Finite G] (σ τ : G) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard ≠ 0
      ↔ ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) τ := by
  constructor
  · intro hne
    obtain ⟨g, k, hk, hgk⟩ := Set.nonempty_of_ncard_ne_zero hne
    exact ⟨k, hk, isConj_iff.mpr ⟨g, hgk⟩⟩
  · rintro ⟨k, hk, hconj⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    exact Set.ncard_ne_zero_of_mem (a := g) ⟨k, hk, hg⟩ (Set.toFinite _)
