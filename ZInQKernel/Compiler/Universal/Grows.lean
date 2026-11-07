import ZInQKernel.Compiler.Circuits

/-!
# Constructions only extend the variable and node lists

`Grows μ m` says that, from every state, the construction `m` only appends to the list of
explicit variables and to the node list, keeps the nodes other than call nodes pairwise
distinct (hash-consing), and creates only constants among `0, 1, 2, 4, -1, μ`. Every builder
operation, macro (in hierarchical mode) and the packed-history construction (with `μ` its
program length) grows; hence the explicit variables of a compiled circuit begin with its inputs,
its node list begins with their variable nodes, and its constants are among
`0, 1, 2, 4, -1, m`.

(Helper lemmas for `compiler/natural/universal/halting-polynomial.md` and
`precision-circuit-specialization.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Universal

open Syntax Natural

/-- The nodes other than call nodes. -/
def nonCall (l : List NatNode) : List NatNode := l.filter fun n => !n.isCall

/-- The constants `0, 1, 2, 4, -1` of the builder and of the packed construction, and one more
constant `μ` (the program length). -/
def ConstSet (μ : ℤ) : Set ℤ := {0, 1, 2, 4, -1, μ}

/-- Every constant node of `l` has its value in `ConstSet μ`. -/
def ConstsIn (μ : ℤ) (l : List NatNode) : Prop := ∀ c, NatNode.const c ∈ l → c ∈ ConstSet μ

/-- `b` is `a` followed by witness variables. -/
def VarsExt (a b : List (ℕ × VarKind)) : Prop := ∃ l, b = a ++ l ∧ ∀ v ∈ l, v.2 = .witness

theorem VarsExt.refl (a : List (ℕ × VarKind)) : VarsExt a a := ⟨[], by simp, by simp⟩

theorem VarsExt.trans {a b c : List (ℕ × VarKind)} (h : VarsExt a b) (h' : VarsExt b c) :
    VarsExt a c := by
  obtain ⟨l, rfl, hl⟩ := h
  obtain ⟨l', rfl, hl'⟩ := h'
  refine ⟨l ++ l', by simp, fun v hv => ?_⟩
  rcases List.mem_append.1 hv with h | h
  · exact hl v h
  · exact hl' v h

/-- The construction `m` only appends witness variables and nodes, keeps the nodes other than
call nodes pairwise distinct (hash-consing), and creates constant nodes only with values in
`ConstSet μ`. -/
def Grows (μ : ℤ) {α : Type} (m : NM α) : Prop :=
  ∀ s, VarsExt s.vars (m s).2.vars ∧ s.nodes <+: (m s).2.nodes ∧
    ((nonCall s.nodes).Nodup → (nonCall (m s).2.nodes).Nodup) ∧
    (ConstsIn μ s.nodes → ConstsIn μ (m s).2.nodes)

variable {μ : ℤ}

namespace Grows

variable {α β : Type}

theorem pure (a : α) : Grows μ (Pure.pure a : NM α) := fun _ =>
  ⟨VarsExt.refl _, List.prefix_refl _, id, id⟩

theorem bind {m : NM α} {f : α → NM β} (hm : Grows μ m) (hf : ∀ a, Grows μ (f a)) :
    Grows μ (m >>= f) := fun s =>
  ⟨VarsExt.trans (hm s).1 (hf _ _).1, (hm s).2.1.trans (hf _ _).2.1,
    fun h => (hf _ _).2.2.1 ((hm s).2.2.1 h), fun h => (hf _ _).2.2.2 ((hm s).2.2.2 h)⟩

theorem bind' {m : NM α} {f : α → NM β} (hf : ∀ a, Grows μ (f a)) (hm : Grows μ m) :
    Grows μ (m >>= f) := bind hm hf

theorem node (n : NatNode) (hn : ∀ c, n = .const c → c ∈ ConstSet μ) :
    Grows μ (Natural.node n) := fun s => by
  refine ⟨by rw [(node_spec n s).2.1]; exact VarsExt.refl _, (node_spec n s).2.2.2, fun h => ?_,
    fun h => ?_⟩
  swap
  · unfold Natural.node
    split
    · exact h
    · intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact h c hc
      · exact hn c (List.mem_singleton.1 hc).symm
  unfold Natural.node
  split
  · exact h
  · rename_i hn
    rw [List.idxOf?_eq_none_iff] at hn
    simp only [nonCall, List.filter_append] at h ⊢
    refine List.nodup_append.2 ⟨h, (List.nodup_singleton n).filter _, fun a ha b hb => ?_⟩
    rintro rfl
    have h1 := (List.mem_filter.1 ha).1
    have h2 := List.mem_singleton.1 (List.mem_filter.1 hb).1
    exact hn (h2 ▸ h1)

theorem constant {c : ℤ} (hc : c ∈ ConstSet μ) : Grows μ (Natural.constant c) :=
  (node (.const c) fun _ h => by cases h; exact hc).bind fun _ => pure _

theorem node_noConst {n : NatNode} (hn : ∀ c, n ≠ .const c) : Grows μ (Natural.node n) :=
  node n fun c h => absurd h (hn c)

theorem addFrom (acc : Ex) (l : List Ex) : Grows μ (Natural.addFrom acc l) := by
  induction l generalizing acc with
  | nil => exact pure _
  | cons y ys ih => exact (node_noConst fun _ h => by cases h).bind fun _ => ih _

theorem mulFrom (acc : Ex) (l : List Ex) : Grows μ (Natural.mulFrom acc l) := by
  induction l generalizing acc with
  | nil => exact pure _
  | cons y ys ih => exact (node_noConst fun _ h => by cases h).bind fun _ => ih _

theorem addL (l : List Ex) : Grows μ (Natural.addL l) := by
  cases l with
  | nil => exact constant (by simp [ConstSet])
  | cons x xs => exact addFrom _ _

theorem mulL (l : List Ex) : Grows μ (Natural.mulL l) := by
  cases l with
  | nil => exact constant (by simp [ConstSet])
  | cons x xs => exact mulFrom _ _

theorem square (x : Ex) : Grows μ (Natural.square x) := mulL _

theorem scale {n : ℤ} (hn : n ∈ ConstSet μ) (x : Ex) : Grows μ (Natural.scale n x) :=
  (constant hn).bind fun _ => mulL _

theorem note (k : MacroKind) : Grows μ (Natural.note k) := fun _ =>
  ⟨VarsExt.refl _, List.prefix_refl _, id, id⟩

theorem fresh : Grows μ Natural.fresh := fun s => by
  have h := node_noConst (μ := μ) (n := .var s.next) (fun _ => nofun)
    { s with next := s.next + 1, vars := s.vars ++ [(s.next, .witness)] }
  exact ⟨VarsExt.trans ⟨[(s.next, .witness)], rfl, by simp⟩ h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem callPower (P Q R : Ex) : Grows μ (Natural.callPower P Q R) := fun _ =>
  ⟨VarsExt.refl _, List.prefix_append _ _, fun h => by
    simpa [Natural.callPower, nonCall, List.filter_append, NatNode.isCall] using h,
    fun h c hc => h c (by simpa [Natural.callPower] using hc)⟩

theorem seqM_cons {m : NM α} {ms : List (NM α)} (hm : Grows μ m) (hms : Grows μ (seqM ms)) :
    Grows μ (seqM (m :: ms)) :=
  hm.bind fun _ => hms.bind fun _ => pure _

theorem seqM_nil : Grows μ (seqM ([] : List (NM α))) := pure _

theorem seqM_all : ∀ (ms : List (NM α)), (∀ m ∈ ms, Grows μ m) → Grows μ (seqM ms)
  | [], _ => seqM_nil
  | m :: ms, h => seqM_cons (h m List.mem_cons_self) (seqM_all ms fun m' hm => h m'
      (List.mem_cons_of_mem _ hm))

theorem andM {ms : List (NM NForm)} (h : Grows μ (seqM ms)) : Grows μ (Natural.andM ms) :=
  h.bind fun _ => pure _

theorem orM {ms : List (NM NForm)} (h : Grows μ (seqM ms)) : Grows μ (Natural.orM ms) :=
  h.bind fun _ => pure _

end Grows

set_option hygiene false in
/-- Proves that a construction grows. -/
macro "grows_tac" : tactic => `(tactic| repeat' (first
  | with_reducible exact Grows.pure _
  | with_reducible exact Grows.fresh
  | with_reducible exact Grows.note _
  | with_reducible exact Grows.constant (by simp [ConstSet])
  | with_reducible exact Grows.addL _
  | with_reducible exact Grows.mulL _
  | with_reducible exact Grows.square _
  | with_reducible exact Grows.scale (by simp [ConstSet]) _
  | with_reducible exact Grows.callPower _ _ _
  | with_reducible exact Grows.seqM_nil
  | with_reducible exact Grows.lt _ _
  | with_reducible exact Grows.odd _
  | with_reducible exact Grows.power _ _ _
  | with_reducible exact Grows.binomial _ _ _
  | with_reducible exact Grows.orthogonal _ _
  | with_reducible exact Grows.mask _ _
  | with_reducible exact Grows.bitAnd _ _ _
  | (with_reducible apply Grows.andM)
  | (with_reducible apply Grows.orM)
  | (with_reducible apply Grows.seqM_cons)
  | (with_reducible apply Grows.bind'; intro _)))

namespace Grows

theorem lt (a b : Ex) : Grows μ (Natural.lt a b) := by unfold Natural.lt; grows_tac
theorem odd (a : Ex) : Grows μ (Natural.odd a) := by unfold Natural.odd; grows_tac
theorem power (P Q R : Ex) : Grows μ (Natural.power .hierarchical P Q R) := by
  unfold Natural.power; grows_tac
theorem binomial (C N K : Ex) : Grows μ (Natural.binomial .hierarchical C N K) := by
  unfold Natural.binomial; grows_tac
theorem orthogonal (a b : Ex) : Grows μ (Natural.orthogonal .hierarchical a b) := by
  unfold Natural.orthogonal; grows_tac
theorem mask (a b : Ex) : Grows μ (Natural.mask .hierarchical a b) := by
  unfold Natural.mask; grows_tac
theorem bitAnd (z x y : Ex) : Grows μ (Natural.bitAnd .hierarchical z x y) := by
  unfold Natural.bitAnd; grows_tac

theorem encode (τ : ExPoly) (φ : NForm) : Grows μ (φ.encode τ) := by
  induction φ using NForm.induct' with
  | eq a b => exact (scale (by simp [ConstSet]) _).bind fun _ => addL _
  | atom f => exact pure _
  | call A B C w j => exact pure _
  | and fs ih =>
    have hl : Grows μ (NForm.encodeList τ fs) := by
      induction fs with
      | nil => exact pure _
      | cons φ fs ihl =>
        exact (ih φ List.mem_cons_self).bind fun _ =>
          (ihl fun ψ hψ => ih ψ (List.mem_cons_of_mem _ hψ)).bind fun _ => pure _
    exact hl.bind fun es => (seqM_all _ fun m hm => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hm; exact square x).bind fun _ => addL _
  | or fs ih =>
    have hl : Grows μ (NForm.encodeList τ fs) := by
      induction fs with
      | nil => exact pure _
      | cons φ fs ihl =>
        exact (ih φ List.mem_cons_self).bind fun _ =>
          (ihl fun ψ hψ => ih ψ (List.mem_cons_of_mem _ hψ)).bind fun _ => pure _
    exact hl.bind fun _ => mulL _

end Grows

/-- The circuit of a growing construction lists its inputs first and then only witnesses, its
node list begins with
their variable nodes, its nodes other than call nodes are pairwise distinct, and its constants
lie in `ConstSet μ`. -/
theorem toCircuit_prefix {k : ℕ} {m : NM NForm} (hm : Grows μ m) :
    VarsExt (State.init k).vars (m.toCircuit k).explicitVars ∧
      (State.init k).nodes <+: (m.toCircuit k).nodes ∧ (nonCall (m.toCircuit k).nodes).Nodup ∧
      ConstsIn μ (m.toCircuit k).nodes := by
  have h1 := hm (State.init k)
  have h2 := Grows.encode (μ := μ) ExPoly.empty (m (State.init k)).1 (m (State.init k)).2
  have h0 : (nonCall (State.init k).nodes).Nodup := by
    simp only [State.init, nonCall]
    refine (List.Nodup.map (fun i j h => by simpa using h) List.nodup_range).filter _
  have hc0 : ConstsIn μ (State.init k).nodes := fun c hc => by simp [State.init] at hc
  exact ⟨VarsExt.trans h1.1 h2.1, h1.2.1.trans h2.2.1, h2.2.2.1 (h1.2.2.1 h0), h2.2.2.2 (h1.2.2.2 hc0)⟩

open Packed RM

theorem grows_freshN (n : ℕ) : Grows μ (freshN n) := by
  induction n with
  | zero => exact Grows.pure _
  | succ n ih => exact Grows.fresh.bind fun _ => ih.bind fun _ => Grows.pure _

theorem grows_appendM {m₁ m₂ : NM (List NForm)} (h₁ : Grows μ m₁) (h₂ : Grows μ m₂) :
    Grows μ (appendM m₁ m₂) := h₁.bind fun _ => h₂.bind fun _ => Grows.pure _

theorem grows_seqConcat : ∀ (ms : List (NM (List NForm))), (∀ m ∈ ms, Grows μ m) →
    Grows μ (seqConcat ms)
  | [], _ => Grows.pure _
  | m :: ms, h => grows_appendM (h m List.mem_cons_self)
      (grows_seqConcat ms fun m' hm => h m' (List.mem_cons_of_mem _ hm))

theorem grows_subBranches (zero : Ex) (S N : List Ex) (i : ℕ) (p : Program) :
    Grows μ (subBranches zero S N i p) := by
  induction p generalizing i with
  | nil => exact Grows.pure _
  | cons ins rest ih =>
    cases ins with
    | dec j x y =>
      exact Grows.fresh.bind fun V => Grows.fresh.bind fun W =>
        (Grows.seqM_cons (Grows.bitAnd _ _ _) (Grows.seqM_cons ((Grows.addL _).bind fun _ =>
          Grows.pure _) Grows.seqM_nil)).bind fun _ => (ih _).bind fun _ => Grows.pure _
    | inc j x => exact ih _
    | halt => exact ih _

theorem grows_construction (p : Program) (r k : ℕ) :
    Grows (p.length : ℤ) (construction p r k) := by
  unfold construction
  refine (Grows.constant (by simp [ConstSet])).bind fun zero =>
    (Grows.constant (by simp [ConstSet])).bind fun one => ?_
  refine Grows.fresh.bind fun q => Grows.fresh.bind fun c => Grows.fresh.bind fun K => ?_
  refine Grows.fresh.bind fun B => Grows.fresh.bind fun T => Grows.fresh.bind fun F => ?_
  refine Grows.fresh.bind fun D => (grows_freshN _).bind fun R => (grows_freshN _).bind
    fun N => ?_
  refine (grows_freshN _).bind fun S => ?_
  refine Grows.bind ?_ fun _ => Grows.pure _
  unfold packedFormulas
  refine grows_appendM ?_ (grows_appendM ?_ (grows_appendM ?_ (grows_appendM ?_ ?_)))
  · unfold items1
    refine Grows.seqM_all _ fun m hm => ?_
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_nil_iff, or_false] at hm
    rcases hm with (rfl | rfl | rfl | rfl | rfl) | ⟨ai, -, rfl⟩
    · exact Grows.lt _ _
    · exact (Grows.constant (by simp [ConstSet])).bind fun _ => Grows.power _ _ _
    · exact (Grows.scale (by simp [ConstSet]) _).bind fun _ => Grows.pure _
    · exact (Grows.constant (by simp [ConstSet])).bind fun _ => Grows.lt _ _
    · exact Grows.power _ _ _
    · exact Grows.lt _ _
  · unfold items2
    refine Grows.seqM_all _ fun m hm => ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact (Grows.mulL _).bind fun _ => (Grows.addL _).bind fun _ => (Grows.mulL _).bind
        fun _ => (Grows.addL _).bind fun _ => Grows.pure _
    · exact (Grows.addL _).bind fun _ => (Grows.mulL _).bind fun _ => Grows.pure _
    · exact (Grows.addL _).bind fun _ => Grows.pure _
    · exact Grows.pure _
  · unfold items3
    refine Grows.seqM_all _ fun m hm => ?_
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hm
    exact Grows.mask _ _
  · unfold items4
    refine grows_seqConcat _ fun m hm => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hm
    unfold registerMasks
    exact Grows.seqM_cons (Grows.mask _ _) (Grows.seqM_cons (Grows.lt _ _) (Grows.seqM_cons
      ((Grows.mulL _).bind fun _ => (Grows.addL _).bind fun _ => (Grows.mulL _).bind fun _ =>
        Grows.bitAnd _ _ _) Grows.seqM_nil))
  · refine (grows_subBranches _ _ _ _ _).bind fun sb => grows_appendM (Grows.pure _) ?_
    refine grows_appendM ?_ ?_
    · unfold items6
      refine Grows.seqM_all _ fun m hm => ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hm
      unfold registerEq
      exact (Grows.addL _).bind fun _ => (Grows.mulL _).bind fun _ => (Grows.addL _).bind
        fun _ => (Grows.mulL _).bind fun _ => (Grows.addL _).bind fun _ => (Grows.mulL _).bind
          fun _ => (Grows.addL _).bind fun _ => Grows.pure _
    · unfold items7
      refine Grows.seqM_all _ fun m hm => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hm
      unfold stateEq
      exact (Grows.addL _).bind fun _ => (Grows.mulL _).bind fun _ => (Grows.addL _).bind
        fun _ => Grows.pure _

/-- The compiled circuit lists its inputs first and then only witnesses, its node list begins
with their variable
nodes, its nodes other than call nodes are pairwise distinct, and its constants are among
`0, 1, 2, 4, -1, m`. -/
theorem compiled_prefix (p : Program) (r k : ℕ) :
    VarsExt (State.init k).vars (compiled p r k).explicitVars ∧
      (State.init k).nodes <+: (compiled p r k).nodes ∧ (nonCall (compiled p r k).nodes).Nodup ∧
      ConstsIn p.length (compiled p r k).nodes :=
  toCircuit_prefix (grows_construction p r k)

end ZInQ.Compiler.Universal
