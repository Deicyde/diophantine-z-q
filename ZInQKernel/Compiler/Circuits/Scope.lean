import ZInQKernel.Compiler.Circuits.Counts
import ZInQKernel.Compiler.Circuits.Builder

/-!
# Well-scopedness of the circuits of constructions

A state invariant: the call nodes are exactly the recorded blocks, in order; the blocks lie in
`[k, c)` for the counter `c`, increase and avoid the explicit variables; the explicit variables
and the blocks cover `[0, c)`; every variable node refers to an explicit variable. Every
builder operation preserves it (`Pres`), hence every construction built from them, and the
natural circuit of such a construction is well scoped (`toCircuit_wellScoped`).
-/

noncomputable section

namespace ZInQ.Compiler.Natural

open Syntax MvPolynomial

/-- The block start of a call node. -/
def NatNode.callW : NatNode → Option ℕ
  | .call _ _ _ w => some w
  | _ => none

/-- The scope invariant of a construction with `k` inputs. -/
structure ScopeInv (k : ℕ) (s : State) : Prop where
  calls : s.nodes.filterMap NatNode.callW = s.blocks
  next_ge : k ≤ s.next
  block_range : ∀ w ∈ s.blocks, k ≤ w ∧ w + powerWitnesses ≤ s.next
  blocks_inc : s.blocks.Pairwise fun w w' => w + powerWitnesses ≤ w'
  blocks_vars : ∀ w ∈ s.blocks, ∀ v ∈ s.vars, ¬ NatCircuit.InBlock w v.1
  vars_lt : ∀ v ∈ s.vars, v.1 < s.next
  cover : ∀ i < s.next, (∃ v ∈ s.vars, v.1 = i) ∨ ∃ w ∈ s.blocks, NatCircuit.InBlock w i
  var_explicit : ∀ i, NatNode.var i ∈ s.nodes → ∃ v ∈ s.vars, v.1 = i

/-- A construction preserves the scope invariant. -/
def Pres {α : Type} (k : ℕ) (m : NM α) : Prop := ∀ s, ScopeInv k s → ScopeInv k (m s).2

namespace Pres

variable {α β : Type} {k : ℕ}

theorem pure (a : α) : Pres k (Pure.pure a : NM α) := fun _ h => h

theorem bind {m : NM α} {f : α → NM β} (hm : Pres k m) (hf : ∀ a, Pres k (f a)) :
    Pres k (m >>= f) := fun s h => hf _ _ (hm s h)

theorem bind' {m : NM α} {f : α → NM β} (hf : ∀ a, Pres k (f a)) (hm : Pres k m) :
    Pres k (m >>= f) := bind hm hf

theorem node {n : NatNode} (hv : ∀ i, n ≠ .var i) (hc : n.callW = none) :
    Pres k (Natural.node n) := fun s h => by
  unfold Natural.node
  split
  · exact h
  · refine ⟨?_, h.next_ge, h.block_range, h.blocks_inc, h.blocks_vars, h.vars_lt, h.cover,
      fun i hi => ?_⟩
    · simp [List.filterMap_append, hc, h.calls]
    · simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with hi | hi
      · exact h.var_explicit i hi
      · exact absurd hi.symm (hv i)

theorem constant (c : ℤ) : Pres k (Natural.constant c) :=
  (node (fun i => by simp) rfl).bind fun _ => pure _

theorem addFrom (acc : Ex) (l : List Ex) : Pres k (Natural.addFrom acc l) := by
  induction l generalizing acc with
  | nil => exact pure _
  | cons y ys ih => exact (node (fun i => by simp) rfl).bind fun _ => ih _

theorem mulFrom (acc : Ex) (l : List Ex) : Pres k (Natural.mulFrom acc l) := by
  induction l generalizing acc with
  | nil => exact pure _
  | cons y ys ih => exact (node (fun i => by simp) rfl).bind fun _ => ih _

theorem addL (l : List Ex) : Pres k (Natural.addL l) := by
  cases l with
  | nil => exact constant 0
  | cons x xs => exact addFrom x xs

theorem mulL (l : List Ex) : Pres k (Natural.mulL l) := by
  cases l with
  | nil => exact constant 1
  | cons x xs => exact mulFrom x xs

theorem square (x : Ex) : Pres k (Natural.square x) := mulL _

theorem scale (n : ℤ) (x : Ex) : Pres k (Natural.scale n x) :=
  (constant n).bind fun _ => mulL _

theorem note (j : MacroKind) : Pres k (Natural.note j) := fun _ h =>
  ⟨h.calls, h.next_ge, h.block_range, h.blocks_inc, h.blocks_vars, h.vars_lt, h.cover,
    h.var_explicit⟩

theorem fresh : Pres k Natural.fresh := fun s h => by
  set s' : State := { s with next := s.next + 1, vars := s.vars ++ [(s.next, .witness)] }
  have h' : ScopeInv k s' := by
    refine ⟨h.calls, by simp [s']; have := h.next_ge; omega, fun w hw => ?_, h.blocks_inc,
      fun w hw v hv => ?_, fun v hv => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · have := h.block_range w hw; simp [s']; omega
    · simp only [s', List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact h.blocks_vars w hw v hv
      · have := h.block_range w hw; simp only [NatCircuit.InBlock, not_and]; omega
    · simp only [s', List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · have := h.vars_lt v hv; simp [s']; omega
      · simp [s']
    · simp only [s'] at hi
      rcases Nat.lt_or_ge i s.next with hi' | hi'
      · rcases h.cover i hi' with ⟨v, hv, rfl⟩ | ⟨w, hw, hiw⟩
        · exact Or.inl ⟨v, by simp [s', hv], rfl⟩
        · exact Or.inr ⟨w, hw, hiw⟩
      · exact Or.inl ⟨(s.next, .witness), by simp [s'], by omega⟩
    · obtain ⟨v, hv, h'⟩ := h.var_explicit i hi
      exact ⟨v, by simp [s', hv], h'⟩
  simp only [Natural.fresh]
  unfold Natural.node
  split
  · exact h'
  · refine ⟨by simp only [List.filterMap_append]; rw [h.calls]; simp [NatNode.callW], h'.next_ge,
      h'.block_range, h'.blocks_inc, h'.blocks_vars, h'.vars_lt, h'.cover, fun i hi => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | hi
    · exact h'.var_explicit i hi
    · cases hi; exact ⟨(s.next, .witness), by simp [s'], rfl⟩

theorem callPower (P Q R : Ex) : Pres k (Natural.callPower P Q R) := fun s h => by
  simp only [Natural.callPower]
  have hn : ∀ x, x < s.next + powerWitnesses ↔ x < s.next + powerWitnesses := fun _ => Iff.rfl
  refine ⟨by rw [List.filterMap_append, h.calls]; simp [NatNode.callW], by
      have := h.next_ge; simp; omega, fun w hw => ?_, ?_, fun w hw v hv => ?_, fun v hv => ?_,
    fun i hi => ?_, fun i hi => ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at hw
    show k ≤ w ∧ w + powerWitnesses ≤ s.next + powerWitnesses
    rcases hw with hw | rfl
    · have := h.block_range w hw; omega
    · exact ⟨h.next_ge, le_rfl⟩
  · rw [List.pairwise_append]
    refine ⟨h.blocks_inc, by simp, fun w hw w' hw' => ?_⟩
    simp only [List.mem_singleton] at hw'
    rw [hw']; exact (h.block_range w hw).2
  · simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact h.blocks_vars w hw v hv
    · have := h.vars_lt v hv; simp only [NatCircuit.InBlock, not_and]; omega
  · have := h.vars_lt v hv; show v.1 < s.next + powerWitnesses; omega
  · change i < s.next + powerWitnesses at hi
    rcases Nat.lt_or_ge i s.next with hi' | hi'
    · rcases h.cover i hi' with h1 | ⟨w, hw, hiw⟩
      · exact Or.inl h1
      · exact Or.inr ⟨w, by simp [hw], hiw⟩
    · exact Or.inr ⟨s.next, by simp, hi', by omega⟩
  · simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | hi
    · exact h.var_explicit i hi
    · cases hi

theorem seqM_cons {m : NM α} {ms : List (NM α)} (hm : Pres k m) (hms : Pres k (seqM ms)) :
    Pres k (seqM (m :: ms)) :=
  hm.bind fun _ => hms.bind fun _ => pure _

theorem seqM_nil : Pres k (seqM ([] : List (NM α))) := pure _

theorem seqM_all : ∀ (ms : List (NM α)), (∀ m ∈ ms, Pres k m) → Pres k (seqM ms)
  | [], _ => seqM_nil
  | m :: ms, h => seqM_cons (h m List.mem_cons_self) (seqM_all ms fun m' hm => h m'
      (List.mem_cons_of_mem _ hm))

theorem andM {ms : List (NM NForm)} (h : Pres k (seqM ms)) : Pres k (Natural.andM ms) :=
  h.bind fun _ => pure _

theorem orM {ms : List (NM NForm)} (h : Pres k (seqM ms)) : Pres k (Natural.orM ms) :=
  h.bind fun _ => pure _

end Pres

set_option hygiene false in
/-- Proves that a construction preserves the scope invariant. -/
macro "pres_tac" : tactic => `(tactic| repeat' (first
  | with_reducible exact Pres.pure _
  | with_reducible exact Pres.fresh
  | with_reducible exact Pres.note _
  | with_reducible exact Pres.constant _
  | with_reducible exact Pres.addL _
  | with_reducible exact Pres.mulL _
  | with_reducible exact Pres.square _
  | with_reducible exact Pres.scale _ _
  | with_reducible exact Pres.callPower _ _ _
  | with_reducible exact Pres.seqM_nil
  | with_reducible exact Pres.lt _ _
  | with_reducible exact Pres.divides _ _
  | with_reducible exact Pres.congruent _ _ _
  | with_reducible exact Pres.odd _
  | with_reducible exact Pres.alpha _ _ _
  | with_reducible exact Pres.powerFlat _ _ _
  | with_reducible exact Pres.power _ _ _ _
  | with_reducible exact Pres.binomial _ _ _ _
  | with_reducible exact Pres.orthogonal _ _ _
  | with_reducible exact Pres.mask _ _ _
  | with_reducible exact Pres.bitAnd _ _ _ _
  | (with_reducible apply Pres.andM)
  | (with_reducible apply Pres.orM)
  | (with_reducible apply Pres.seqM_cons)
  | (with_reducible apply Pres.bind'; intro _)))

namespace Pres

variable {k : ℕ}

theorem lt (a b : Ex) : Pres k (Natural.lt a b) := by unfold Natural.lt; pres_tac
theorem divides (a b : Ex) : Pres k (Natural.divides a b) := by unfold Natural.divides; pres_tac
theorem congruent (a M b : Ex) : Pres k (Natural.congruent a M b) := by
  unfold Natural.congruent; pres_tac
theorem odd (a : Ex) : Pres k (Natural.odd a) := by unfold Natural.odd; pres_tac
theorem alpha (X b N : Ex) : Pres k (Natural.alpha X b N) := by unfold Natural.alpha; pres_tac
theorem powerFlat (P Q R : Ex) : Pres k (Natural.powerFlat P Q R) := by
  unfold Natural.powerFlat; pres_tac
theorem power (mode : PowerMode) (P Q R : Ex) : Pres k (Natural.power mode P Q R) := by
  unfold Natural.power; cases mode <;> pres_tac
theorem binomial (mode : PowerMode) (C N K : Ex) : Pres k (Natural.binomial mode C N K) := by
  unfold Natural.binomial; pres_tac
theorem orthogonal (mode : PowerMode) (a b : Ex) : Pres k (Natural.orthogonal mode a b) := by
  unfold Natural.orthogonal; pres_tac
theorem mask (mode : PowerMode) (a b : Ex) : Pres k (Natural.mask mode a b) := by
  unfold Natural.mask; pres_tac
theorem bitAnd (mode : PowerMode) (z x y : Ex) : Pres k (Natural.bitAnd mode z x y) := by
  unfold Natural.bitAnd; pres_tac

theorem encode (τ : ExPoly) (φ : NForm) : Pres k (φ.encode τ) := by
  induction φ using NForm.induct' with
  | eq a b => exact (scale _ _).bind fun _ => addL _
  | atom f => exact pure _
  | call A B C w j => exact pure _
  | and fs ih =>
    have hl : Pres k (NForm.encodeList τ fs) := by
      induction fs with
      | nil => exact pure _
      | cons φ fs ihl =>
        exact (ih φ List.mem_cons_self).bind fun _ =>
          (ihl fun ψ hψ => ih ψ (List.mem_cons_of_mem _ hψ)).bind fun _ => pure _
    exact hl.bind fun es => (seqM_all _ fun m hm => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hm; exact square x).bind fun _ => addL _
  | or fs ih =>
    have hl : Pres k (NForm.encodeList τ fs) := by
      induction fs with
      | nil => exact pure _
      | cons φ fs ihl =>
        exact (ih φ List.mem_cons_self).bind fun _ =>
          (ihl fun ψ hψ => ih ψ (List.mem_cons_of_mem _ hψ)).bind fun _ => pure _
    exact hl.bind fun _ => mulL _

end Pres

theorem scopeInv_init (k : ℕ) : ScopeInv k (State.init k) := by
  refine ⟨by simp [State.init, List.filterMap_map, NatNode.callW], le_rfl, by simp [State.init],
    by simp [State.init], by simp [State.init], fun v hv => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [State.init, List.mem_map, List.mem_range] at hv
    obtain ⟨j, hj, rfl⟩ := hv; exact hj
  · exact Or.inl ⟨(i, .input), by simp [State.init]; exact hi, rfl⟩
  · simp only [State.init, List.mem_map, List.mem_range, NatNode.var.injEq] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact ⟨(j, .input), by simp [State.init]; exact hj, rfl⟩

/-- **Circuits of constructions are well scoped.** -/
theorem toCircuit_wellScoped {k : ℕ} {m : NM NForm} (hm : Pres k m) : (m.toCircuit k).WellScoped := by
  have h := Pres.encode (k := k) ExPoly.empty (m (State.init k)).1 _ (hm _ (scopeInv_init k))
  set s := ((m (State.init k)).1.encode ExPoly.empty (m (State.init k)).2).2
  have hb : (m.toCircuit k).blocks = s.blocks := by
    rw [NatCircuit.blocks, NM.toCircuit_nodes, ← h.calls]
    congr 1
  refine ⟨fun w hw => ?_, ?_, fun w hw v hv => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hb] at hw; exact h.block_range w hw
  · rw [hb]
    refine h.blocks_inc.imp fun {w w'} hww' i hi hi' => ?_
    simp only [NatCircuit.InBlock] at hi hi'; omega
  · rw [hb] at hw; exact h.blocks_vars w hw v hv
  · rw [hb]; exact h.cover i hi
  · exact h.var_explicit i hi

end ZInQ.Compiler.Natural
