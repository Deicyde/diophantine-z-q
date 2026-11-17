import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes.lean
Original Git blob: 5396e279fd36459076e3fde56e7f3479f321dc91
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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


end P2MW.S_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
