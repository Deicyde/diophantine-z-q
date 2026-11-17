/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes

set_option autoImplicit false

open Topology

universe u

theorem solution
    {X : Type u} [TopologicalSpace X] {s : Set X} (hs : Topology.IsConstructible s)
    {x : X} (hx : x ∈ closure s) (hgen : ∀ y ∈ s, x ⤳ y) : x ∈ s := by
  revert hx hgen
  induction s, hs using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun s hs t ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
      fun s hs t ht ↦ ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, .empty⟩
  | top_mem => exact ⟨isOpen_univ, .univ⟩
  | sdiff U hU V hV =>
    intro hx hgen
    have hxV : x ∉ V := fun h =>
      (closure_minimal (fun z hz => hz.2) hV.1.isClosed_compl hx) h
    obtain ⟨y, hy⟩ := closure_nonempty_iff.mp ⟨x, hx⟩
    exact ⟨(hgen y hy).mem_open hU.1 hy.1, hxV⟩
  | sup s _ t _ hs' ht' =>
    intro hx hgen
    change x ∈ closure (s ∪ t) at hx
    rw [closure_union] at hx
    rcases hx with hx | hx
    · exact Or.inl (hs' hx fun y hy => hgen y (Or.inl hy))
    · exact Or.inr (ht' hx fun y hy => hgen y (Or.inr hy))
