import ZInQKernel.Compiler.Circuits.Circuit

/-!
# Soundness of the hash-consing builder

Every node index handed out by the builder denotes the polynomial of the expression it was
created for: an expression `h` is *valid* in a state when its node exists and denotes `h.poly`.
Creating a node appends it, so earlier denotations do not change; returning an existing node
happens only for an equal node, whose denotation is the same because nodes refer only to earlier
nodes. Constructions are specified by triples `Triple P m Q` (from a well-formed state satisfying
`P`, `m` keeps the node list well formed, only extends it, and ends in `Q`), with a bind rule for
monotone preconditions. The node encoding of a valid formula is a valid expression whose
polynomial is `κ(φ)`.
-/

noncomputable section

namespace ZInQ.Compiler.Natural

open Syntax MvPolynomial

/-- The children of a node. -/
def NatNode.children : NatNode → List ℕ
  | .const _ => []
  | .var _ => []
  | .add j k => [j, k]
  | .mul j k => [j, k]
  | .call a b c _ => [a, b, c]

/-- Every node refers only to earlier nodes. -/
def NodesWF (l : List NatNode) : Prop := ∀ j (hj : j < l.length), ∀ i ∈ l[j].children, i < j

variable (T : ExPoly)

theorem denoteNatNodes_append (l : List NatNode) (n : NatNode) :
    denoteNatNodes T (l ++ [n]) = denoteNatNodes T l ++ [n.denote T (denoteNatNodes T l)] := by
  simp [denoteNatNodes, List.foldl_append]

theorem length_denoteNatNodes (l : List NatNode) : (denoteNatNodes T l).length = l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l n ih => simp [denoteNatNodes_append, ih]

theorem getPoly_denoteNatNodes_append {l l' : List NatNode} {i : ℕ} (hi : i < l.length) :
    getPoly (denoteNatNodes T (l ++ l')) i = getPoly (denoteNatNodes T l) i := by
  induction l' using List.reverseRecOn with
  | nil => simp
  | append_singleton l' n ih =>
    rw [← List.append_assoc, denoteNatNodes_append, getPoly, List.getD_append _ _ _ _
      (by rw [length_denoteNatNodes]; simp; omega)]
    exact ih

theorem getPoly_prefix {l l' : List NatNode} (h : l <+: l') {i : ℕ} (hi : i < l.length) :
    getPoly (denoteNatNodes T l') i = getPoly (denoteNatNodes T l) i := by
  obtain ⟨t, rfl⟩ := h
  exact getPoly_denoteNatNodes_append T hi

theorem NatNode.denote_congr {n : NatNode} {vals vals' : List Poly}
    (h : ∀ i ∈ n.children, getPoly vals i = getPoly vals' i) : n.denote T vals = n.denote T vals' := by
  cases n <;> simp_all [NatNode.denote, NatNode.children]

/-- In a well-formed node list, node `j` denotes its node over all nodes. -/
theorem getPoly_denoteNatNodes_of_wf {l : List NatNode} (hwf : NodesWF l) {j : ℕ}
    (hj : j < l.length) : getPoly (denoteNatNodes T l) j = l[j].denote T (denoteNatNodes T l) := by
  have h1 : getPoly (denoteNatNodes T l) j = l[j].denote T (denoteNatNodes T (l.take j)) :=
    getD_foldl_snoc _ l hj 0
  rw [h1]
  refine NatNode.denote_congr T fun i hi => ?_
  have hij := hwf j hj i hi
  rw [← getPoly_prefix T (List.take_prefix j l) (by simp; omega)]

/-- The polynomials of the nodes of a state. -/
def State.vals (s : State) : List Poly := denoteNatNodes T s.nodes

/-- `h` is a node of `s` denoting `h.poly`. -/
def Ex.Valid (s : State) (h : Ex) : Prop :=
  h.node < s.nodes.length ∧ getPoly (s.vals T) h.node = h.poly

theorem Ex.Valid.mono {s s' : State} {h : Ex} (hv : h.Valid T s) (hs : s.nodes <+: s'.nodes) :
    h.Valid T s' :=
  ⟨lt_of_lt_of_le hv.1 hs.length_le, (getPoly_prefix T hs hv.1).trans hv.2⟩

/-- All expressions of a formula are valid; a call atom's node denotes the call. -/
def NForm.Valid (s : State) : NForm → Prop
  | .eq a b => a.Valid T s ∧ b.Valid T s
  | .atom f => f.Valid T s
  | .call P Q R w j => P.Valid T s ∧ Q.Valid T s ∧ R.Valid T s ∧
      (⟨j, T.call (callArgs P.poly Q.poly R.poly T.params) w⟩ : Ex).Valid T s
  | .and fs => ∀ φ, (_ : φ ∈ fs) → NForm.Valid s φ
  | .or fs => ∀ φ, (_ : φ ∈ fs) → NForm.Valid s φ

theorem NForm.Valid.mono {s s' : State} (hs : s.nodes <+: s'.nodes) :
    ∀ {φ : NForm}, φ.Valid T s → φ.Valid T s'
  | .eq a b, h => by
    simp only [NForm.Valid] at h ⊢; exact ⟨Ex.Valid.mono T h.1 hs, Ex.Valid.mono T h.2 hs⟩
  | .atom f, h => by simp only [NForm.Valid] at h ⊢; exact Ex.Valid.mono T h hs
  | .call P Q R w j, h => by
    simp only [NForm.Valid] at h ⊢
    exact ⟨Ex.Valid.mono T h.1 hs, Ex.Valid.mono T h.2.1 hs, Ex.Valid.mono T h.2.2.1 hs,
      Ex.Valid.mono T h.2.2.2 hs⟩
  | .and fs, h => by
    simp only [NForm.Valid] at h ⊢; exact fun φ hφ => NForm.Valid.mono hs (h φ hφ)
  | .or fs, h => by
    simp only [NForm.Valid] at h ⊢; exact fun φ hφ => NForm.Valid.mono hs (h φ hφ)

/-! ### Triples -/

/-- From a well-formed state satisfying `P`, `m` keeps the node list well formed, only extends
it, and ends in `Q`. -/
def Triple {α : Type} (P : State → Prop) (m : NM α) (Q : α → State → Prop) : Prop :=
  ∀ s, NodesWF s.nodes → P s → NodesWF (m s).2.nodes ∧ s.nodes <+: (m s).2.nodes ∧ Q (m s).1 (m s).2

/-- A precondition that survives extensions of the node list. -/
def Mono (P : State → Prop) : Prop := ∀ s s', s.nodes <+: s'.nodes → P s → P s'

namespace Mono

theorem and {P Q : State → Prop} (hP : Mono P) (hQ : Mono Q) : Mono fun s => P s ∧ Q s :=
  fun s s' hs h => ⟨hP s s' hs h.1, hQ s s' hs h.2⟩

theorem true : Mono fun _ => True := fun _ _ _ _ => trivial

theorem valid (h : Ex) : Mono fun s => h.Valid T s := fun _ _ hs hv => hv.mono T hs

theorem nvalid (φ : NForm) : Mono fun s => φ.Valid T s := fun _ _ hs hv => hv.mono T hs

theorem forall_mem {β : Type} (l : List β) {V : β → State → Prop} (hV : ∀ x, Mono (V x)) :
    Mono fun s => ∀ x ∈ l, V x s := fun s s' hs h x hx => hV x s s' hs (h x hx)

end Mono

namespace Triple

variable {T}
variable {α β : Type}

theorem pure {P : State → Prop} {Q : α → State → Prop} (a : α) (h : ∀ s, P s → Q a s) :
    Triple P (Pure.pure a : NM α) Q := fun s hwf hs => ⟨hwf, List.prefix_refl _, h s hs⟩

theorem bind {P : State → Prop} {m : NM α} {f : α → NM β} {Q : α → State → Prop}
    {R : β → State → Prop} (hP : Mono P) (hm : Triple P m Q)
    (hf : ∀ a, Triple (fun s => P s ∧ Q a s) (f a) R) : Triple P (m >>= f) R := fun s hwf hs => by
  obtain ⟨h1, h2, h3⟩ := hm s hwf hs
  obtain ⟨k1, k2, k3⟩ := hf (m s).1 (m s).2 h1 ⟨hP s _ h2 hs, h3⟩
  exact ⟨k1, h2.trans k2, k3⟩

theorem bind' {P : State → Prop} {m : NM α} {f : α → NM β} {Q : α → State → Prop}
    {R : β → State → Prop} (hm : Triple P m Q)
    (hf : ∀ a, Triple (fun s => P s ∧ Q a s) (f a) R) (hP : Mono P) : Triple P (m >>= f) R :=
  bind hP hm hf

theorem post {P : State → Prop} {m : NM α} {Q Q' : α → State → Prop} (h : Triple P m Q)
    (hQ : ∀ a s, Q a s → Q' a s) : Triple P m Q' := fun s hwf hs => by
  obtain ⟨h1, h2, h3⟩ := h s hwf hs
  exact ⟨h1, h2, hQ _ _ h3⟩

theorem pre {P P' : State → Prop} {m : NM α} {Q : α → State → Prop} (h : Triple P m Q)
    (hP : ∀ s, P' s → P s) : Triple P' m Q := fun s hwf hs => h s hwf (hP s hs)

end Triple

theorem node_triple {n : NatNode} {s : State} (hwf : NodesWF s.nodes)
    (hn : ∀ i ∈ n.children, i < s.nodes.length) :
    NodesWF (node n s).2.nodes ∧ s.nodes <+: (node n s).2.nodes ∧
      (node n s).1 < (node n s).2.nodes.length ∧
      getPoly ((node n s).2.vals T) (node n s).1 = n.denote T (s.vals T) := by
  unfold node
  split
  · rename_i j hj
    obtain ⟨hjl, hjn, -⟩ := List.idxOf?_eq_some_iff.1 hj
    refine ⟨hwf, List.prefix_refl _, hjl, ?_⟩
    simp only [State.vals]
    rw [getPoly_denoteNatNodes_of_wf T hwf hjl, hjn]
  · refine ⟨fun j hj i hi => ?_, List.prefix_append _ _, by simp, ?_⟩
    · simp only [List.length_append, List.length_singleton] at hj
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hj) with h | rfl
      · rw [List.getElem_append_left h] at hi; exact hwf j h i hi
      · rw [List.getElem_append_right (by omega)] at hi
        simp only [Nat.sub_self, List.getElem_cons_zero] at hi
        exact hn i hi
    · simp only [State.vals]
      rw [denoteNatNodes_append, getPoly, List.getD_append_right _ _ _ _ (by
        rw [length_denoteNatNodes]), length_denoteNatNodes, Nat.sub_self, List.getD_cons_zero]

/-! ### Builder operations -/

variable {T}

theorem Triple.constant (P : State → Prop) (c : ℤ) :
    Triple P (Natural.constant c) fun h s => h.Valid T s := fun s hwf _ => by
  obtain ⟨h1, h2, h3, h4⟩ := node_triple T (n := .const c) hwf (by simp [NatNode.children])
  exact ⟨h1, h2, h3, h4⟩

theorem Triple.fresh (P : State → Prop) : Triple P Natural.fresh fun h s => h.Valid T s :=
  fun s hwf _ => by
  obtain ⟨h1, h2, h3, h4⟩ := node_triple T (n := .var s.next)
    (s := { s with next := s.next + 1, vars := s.vars ++ [(s.next, .witness)] }) hwf
    (by simp [NatNode.children])
  exact ⟨h1, h2, h3, h4⟩

theorem Triple.note (P : State → Prop) (k : MacroKind) :
    Triple P (Natural.note k) fun _ _ => True := fun _ hwf _ =>
  ⟨hwf, List.prefix_refl _, trivial⟩

theorem triple_addFrom (acc : Ex) (l : List Ex) {s : State} (hwf : NodesWF s.nodes)
    (hacc : acc.Valid T s) (hl : ∀ x ∈ l, x.Valid T s) :
    NodesWF (addFrom acc l s).2.nodes ∧ s.nodes <+: (addFrom acc l s).2.nodes ∧
      (addFrom acc l s).1.Valid T (addFrom acc l s).2 := by
  induction l generalizing acc s with
  | nil => exact ⟨hwf, List.prefix_refl _, hacc⟩
  | cons y ys ih =>
    have hy := hl y List.mem_cons_self
    obtain ⟨h1, h2, h3, h4⟩ := node_triple T (n := .add acc.node y.node) hwf
      (by simp [NatNode.children, hacc.1, hy.1])
    have hv : (⟨(node (.add acc.node y.node) s).1, acc.poly + y.poly⟩ : Ex).Valid T
        (node (.add acc.node y.node) s).2 :=
      ⟨h3, by rw [h4]; simp [NatNode.denote, hacc.2, hy.2]⟩
    obtain ⟨k1, k2, k3⟩ := ih _ h1 hv fun x hx => (hl x (List.mem_cons_of_mem _ hx)).mono T h2
    exact ⟨k1, h2.trans k2, k3⟩

theorem triple_mulFrom (acc : Ex) (l : List Ex) {s : State} (hwf : NodesWF s.nodes)
    (hacc : acc.Valid T s) (hl : ∀ x ∈ l, x.Valid T s) :
    NodesWF (mulFrom acc l s).2.nodes ∧ s.nodes <+: (mulFrom acc l s).2.nodes ∧
      (mulFrom acc l s).1.Valid T (mulFrom acc l s).2 := by
  induction l generalizing acc s with
  | nil => exact ⟨hwf, List.prefix_refl _, hacc⟩
  | cons y ys ih =>
    have hy := hl y List.mem_cons_self
    obtain ⟨h1, h2, h3, h4⟩ := node_triple T (n := .mul acc.node y.node) hwf
      (by simp [NatNode.children, hacc.1, hy.1])
    have hv : (⟨(node (.mul acc.node y.node) s).1, acc.poly * y.poly⟩ : Ex).Valid T
        (node (.mul acc.node y.node) s).2 :=
      ⟨h3, by rw [h4]; simp [NatNode.denote, hacc.2, hy.2]⟩
    obtain ⟨k1, k2, k3⟩ := ih _ h1 hv fun x hx => (hl x (List.mem_cons_of_mem _ hx)).mono T h2
    exact ⟨k1, h2.trans k2, k3⟩

theorem Triple.addL {P : State → Prop} (l : List Ex) (hl : ∀ s, P s → ∀ x ∈ l, x.Valid T s) :
    Triple P (Natural.addL l) fun h s => h.Valid T s := fun s hwf hs => by
  cases l with
  | nil => exact Triple.constant P 0 s hwf hs
  | cons x xs =>
    exact triple_addFrom x xs hwf (hl s hs x List.mem_cons_self)
      fun y hy => hl s hs y (List.mem_cons_of_mem _ hy)

theorem Triple.mulL {P : State → Prop} (l : List Ex) (hl : ∀ s, P s → ∀ x ∈ l, x.Valid T s) :
    Triple P (Natural.mulL l) fun h s => h.Valid T s := fun s hwf hs => by
  cases l with
  | nil => exact Triple.constant P 1 s hwf hs
  | cons x xs =>
    exact triple_mulFrom x xs hwf (hl s hs x List.mem_cons_self)
      fun y hy => hl s hs y (List.mem_cons_of_mem _ hy)

theorem Triple.square {P : State → Prop} (x : Ex) (hx : ∀ s, P s → x.Valid T s) :
    Triple P (Natural.square x) fun h s => h.Valid T s :=
  Triple.mulL [x, x] fun s hs y hy => by simp at hy; rcases hy with rfl | rfl <;> exact hx s hs

theorem Triple.scale {P : State → Prop} (hP : Mono P) (n : ℤ) (x : Ex)
    (hx : ∀ s, P s → x.Valid T s) : Triple P (Natural.scale n x) fun h s => h.Valid T s :=
  Triple.bind hP (Triple.constant P n) fun c => Triple.mulL [c, x] fun s hs y hy => by
    simp at hy; rcases hy with rfl | rfl
    · exact hs.2
    · exact hx s hs.1

theorem Triple.callPower {P : State → Prop} (a b c : Ex)
    (h : ∀ s, P s → a.Valid T s ∧ b.Valid T s ∧ c.Valid T s) :
    Triple P (Natural.callPower a b c) fun φ s => φ.Valid T s := fun s hwf hs => by
  obtain ⟨ha, hb, hc⟩ := h s hs
  have hpre : s.nodes <+: s.nodes ++ [.call a.node b.node c.node s.next] := List.prefix_append _ _
  refine ⟨fun j hj i hi => ?_, hpre, ?_⟩
  · simp only [Natural.callPower, List.length_append, List.length_singleton] at hj hi
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hj) with h' | rfl
    · rw [List.getElem_append_left h'] at hi; exact hwf j h' i hi
    · rw [List.getElem_append_right (by omega)] at hi
      simp [NatNode.children] at hi
      rcases hi with rfl | rfl | rfl
      exacts [ha.1, hb.1, hc.1]
  · simp only [Natural.callPower, NForm.Valid]
    refine ⟨ha.mono T hpre, hb.mono T hpre, hc.mono T hpre, by simp, ?_⟩
    simp only [State.vals]
    rw [denoteNatNodes_append, getPoly, List.getD_append_right _ _ _ _ (by
      rw [length_denoteNatNodes]), length_denoteNatNodes, Nat.sub_self, List.getD_cons_zero]
    simp only [NatNode.denote]
    rw [show getPoly (denoteNatNodes T s.nodes) a.node = a.poly from ha.2,
      show getPoly (denoteNatNodes T s.nodes) b.node = b.poly from hb.2,
      show getPoly (denoteNatNodes T s.nodes) c.node = c.poly from hc.2]

theorem Triple.seqM {α : Type} {P : State → Prop} (hP : Mono P) {V : α → State → Prop}
    (hV : ∀ a, Mono (V a)) :
    ∀ (ms : List (NM α)), (∀ m ∈ ms, Triple P m V) →
      Triple P (Natural.seqM ms) fun l s => ∀ a ∈ l, V a s
  | [], _ => Triple.pure _ fun _ _ a ha => absurd ha List.not_mem_nil
  | m :: ms, h => by
    refine Triple.bind hP (h m List.mem_cons_self) fun a => ?_
    refine Triple.bind (hP.and (hV a)) ((Triple.seqM (hP.and (hV a)) hV ms fun m' hm' =>
      (h m' (List.mem_cons_of_mem _ hm')).pre fun s hs => hs.1)) fun as => ?_
    exact Triple.pure _ fun s hs b hb => by
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hs.1.2
      · exact hs.2 b hb

theorem Triple.andM {P : State → Prop} (ms : List (NM NForm))
    (h : ∀ m ∈ ms, Triple P m fun φ s => φ.Valid T s) (hP : Mono P) :
    Triple P (Natural.andM ms) fun φ s => φ.Valid T s :=
  Triple.bind hP (Triple.seqM hP (fun φ => Mono.nvalid T φ) ms h) fun fs =>
    Triple.pure _ fun s hs => by simp only [NForm.Valid]; exact hs.2

theorem Triple.orM {P : State → Prop} (ms : List (NM NForm))
    (h : ∀ m ∈ ms, Triple P m fun φ s => φ.Valid T s) (hP : Mono P) :
    Triple P (Natural.orM ms) fun φ s => φ.Valid T s :=
  Triple.bind hP (Triple.seqM hP (fun φ => Mono.nvalid T φ) ms h) fun fs =>
    Triple.pure _ fun s hs => by simp only [NForm.Valid]; exact hs.2

end ZInQ.Compiler.Natural

namespace ZInQ.Compiler.Natural

open Syntax MvPolynomial

variable {T : ExPoly}

set_option hygiene false in
/-- Closes monotonicity goals of conjunctions of validity facts. -/
macro "mono_tac" : tactic => `(tactic| repeat' (first
  | exact Mono.true
  | exact Mono.valid T _
  | exact Mono.nvalid T _
  | assumption
  | apply Mono.and))

set_option hygiene false in
/-- Closes validity side goals `∀ s, P s → …` from the conjunctions in `P s`. -/
macro "valid_tac" : tactic => `(tactic| (
  intro s hs
  try simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, NForm.Valid] at ⊢
  casesm* _ ∧ _
  try (obtain ⟨_, _, _⟩ := h s ‹_›)
  try (obtain ⟨_, _⟩ := h s ‹_›)
  try (have := h s ‹_›)
  repeat' (with_reducible apply And.intro)
  all_goals assumption))

/-- Proves validity triples of constructions built from the builder operations and macros. -/
syntax "triple_tac" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| triple_tac) => `(tactic| repeat' (first
    | with_reducible exact Mono.true
    | with_reducible exact Mono.valid T _
    | with_reducible exact Mono.nvalid T _
    | with_reducible apply Mono.and
    | with_reducible assumption
    | with_reducible exact Triple.constant (T := T) _ _
    | with_reducible exact Triple.fresh (T := T) _
    | with_reducible exact Triple.note _ _
    | with_reducible exact Triple.addL (T := T) _ (by valid_tac)
    | with_reducible exact Triple.mulL (T := T) _ (by valid_tac)
    | with_reducible exact Triple.square (T := T) _ (by valid_tac)
    | with_reducible exact Triple.scale (T := T) (by mono_tac) _ _ (by valid_tac)
    | with_reducible exact Triple.callPower (T := T) _ _ _ (by valid_tac)
    | with_reducible exact Triple.lt (T := T) (by mono_tac) (by valid_tac)
    | with_reducible exact Triple.divides (T := T) (by mono_tac) (by valid_tac)
    | with_reducible exact Triple.congruent (T := T) (by mono_tac) (by valid_tac)
    | with_reducible exact Triple.odd (T := T) (by mono_tac) (by valid_tac)
    | with_reducible exact Triple.alpha (T := T) (by mono_tac) (by valid_tac)
    | with_reducible exact Triple.powerFlat (T := T) (by mono_tac) (by valid_tac)
    | with_reducible exact Triple.power (T := T) (by mono_tac) (by valid_tac)
    | with_reducible exact Triple.binomial (T := T) (by mono_tac) (by valid_tac)
    | with_reducible exact Triple.orthogonal (T := T) (by mono_tac) (by valid_tac)
    | with_reducible exact Triple.mask (T := T) (by mono_tac) (by valid_tac)
    | with_reducible exact Triple.bitAnd (T := T) (by mono_tac) (by valid_tac)
    | with_reducible exact Triple.pure _ (by valid_tac)
    | (with_reducible apply Triple.andM
       with_reducible intro m hm
       simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
       repeat' (rcases hm with rfl | hm))
    | (with_reducible apply Triple.orM
       with_reducible intro m hm
       simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
       repeat' (rcases hm with rfl | hm))
    | with_reducible apply Triple.bind'
    | with_reducible intro _))

theorem Triple.lt {P : State → Prop} (hP : Mono P) {a b : Ex}
    (h : ∀ s, P s → a.Valid T s ∧ b.Valid T s) :
    Triple P (Natural.lt a b) fun φ s => φ.Valid T s := by
  unfold Natural.lt; triple_tac

theorem Triple.divides {P : State → Prop} (hP : Mono P) {a b : Ex}
    (h : ∀ s, P s → a.Valid T s ∧ b.Valid T s) :
    Triple P (Natural.divides a b) fun φ s => φ.Valid T s := by
  unfold Natural.divides; triple_tac

theorem Triple.congruent {P : State → Prop} (hP : Mono P) {a M b : Ex}
    (h : ∀ s, P s → a.Valid T s ∧ M.Valid T s ∧ b.Valid T s) :
    Triple P (Natural.congruent a M b) fun φ s => φ.Valid T s := by
  unfold Natural.congruent; triple_tac

theorem Triple.odd {P : State → Prop} (hP : Mono P) {a : Ex} (h : ∀ s, P s → a.Valid T s) :
    Triple P (Natural.odd a) fun φ s => φ.Valid T s := by
  unfold Natural.odd; triple_tac

theorem Triple.alpha {P : State → Prop} (hP : Mono P) {X b N : Ex}
    (h : ∀ s, P s → X.Valid T s ∧ b.Valid T s ∧ N.Valid T s) :
    Triple P (Natural.alpha X b N) fun φ s => φ.Valid T s := by
  unfold Natural.alpha; triple_tac

theorem Triple.powerFlat {P : State → Prop} (hP : Mono P) {A B C : Ex}
    (h : ∀ s, P s → A.Valid T s ∧ B.Valid T s ∧ C.Valid T s) :
    Triple P (Natural.powerFlat A B C) fun φ s => φ.Valid T s := by
  unfold Natural.powerFlat; triple_tac

theorem Triple.power {P : State → Prop} (hP : Mono P) {mode : PowerMode} {A B C : Ex}
    (h : ∀ s, P s → A.Valid T s ∧ B.Valid T s ∧ C.Valid T s) :
    Triple P (Natural.power mode A B C) fun φ s => φ.Valid T s := by
  unfold Natural.power
  cases mode <;> triple_tac

theorem Triple.binomial {P : State → Prop} (hP : Mono P) {mode : PowerMode} {C N K : Ex}
    (h : ∀ s, P s → C.Valid T s ∧ N.Valid T s ∧ K.Valid T s) :
    Triple P (Natural.binomial mode C N K) fun φ s => φ.Valid T s := by
  unfold Natural.binomial; triple_tac

theorem Triple.orthogonal {P : State → Prop} (hP : Mono P) {mode : PowerMode} {a b : Ex}
    (h : ∀ s, P s → a.Valid T s ∧ b.Valid T s) :
    Triple P (Natural.orthogonal mode a b) fun φ s => φ.Valid T s := by
  unfold Natural.orthogonal; triple_tac

theorem Triple.mask {P : State → Prop} (hP : Mono P) {mode : PowerMode} {a b : Ex}
    (h : ∀ s, P s → a.Valid T s ∧ b.Valid T s) :
    Triple P (Natural.mask mode a b) fun φ s => φ.Valid T s := by
  unfold Natural.mask; triple_tac

theorem Triple.bitAnd {P : State → Prop} (hP : Mono P) {mode : PowerMode} {z x y : Ex}
    (h : ∀ s, P s → z.Valid T s ∧ x.Valid T s ∧ y.Valid T s) :
    Triple P (Natural.bitAnd mode z x y) fun φ s => φ.Valid T s := by
  unfold Natural.bitAnd; triple_tac

end ZInQ.Compiler.Natural

namespace ZInQ.Compiler.Natural

open Syntax MvPolynomial

variable {T : ExPoly}

theorem seqM_square_correct (es : List Ex) (s : State) (hwf : NodesWF s.nodes)
    (hv : ∀ e ∈ es, e.Valid T s) :
    NodesWF (seqM (es.map square) s).2.nodes ∧ s.nodes <+: (seqM (es.map square) s).2.nodes ∧
      (∀ x ∈ (seqM (es.map square) s).1, x.Valid T (seqM (es.map square) s).2) ∧
      (seqM (es.map square) s).1.map Ex.poly = es.map fun e => e.poly * e.poly := by
  induction es generalizing s with
  | nil => exact ⟨hwf, List.prefix_refl _, by simp [seqM], by simp [seqM]⟩
  | cons e es ih =>
    have he := hv e List.mem_cons_self
    obtain ⟨h1, h2, h3⟩ := Triple.square (T := T) (P := fun s => e.Valid T s) e (fun _ h => h) s hwf he
    obtain ⟨k1, k2, k3, k4⟩ := ih (square e s).2 h1
      fun x hx => (hv x (List.mem_cons_of_mem _ hx)).mono T h2
    refine ⟨by simpa [seqM] using k1, by simpa [seqM] using h2.trans k2, ?_, ?_⟩
    · intro x hx
      simp only [List.map_cons, seqM, NM.bind_apply, NM.pure_apply, List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · exact h3.mono T k2
      · exact k3 x hx
    · simp only [List.map_cons, seqM, NM.bind_apply, NM.pure_apply]
      rw [k4, ((IsExpr.square e) s).1]

mutual

/-- **Node encoding.** The encoding of a valid formula is a valid expression whose polynomial is
`κ(φ)`. -/
theorem encode_correct : ∀ (φ : NForm) (s : State), NodesWF s.nodes → φ.Valid T s →
    NodesWF (φ.encode T s).2.nodes ∧ s.nodes <+: (φ.encode T s).2.nodes ∧
      (φ.encode T s).1.Valid T (φ.encode T s).2 ∧
      (φ.encode T s).1.poly = (φ.toFormula T).compile
  | .eq a b, s, hwf, hv => by
    simp only [NForm.Valid] at hv
    have h := (Triple.bind (P := fun s => a.Valid T s ∧ b.Valid T s)
      ((Mono.valid T a).and (Mono.valid T b))
      (Triple.scale ((Mono.valid T a).and (Mono.valid T b)) (-1) b fun s hs => hs.2) fun c =>
        Triple.addL [a, c] fun s hs x hx => by
          simp at hx; rcases hx with rfl | rfl
          · exact hs.1.1
          · exact hs.2) s hwf hv
    refine ⟨h.1, h.2.1, h.2.2, ?_⟩
    simp only [NForm.encode, NForm.toFormula, Formula.compile_eq, NM.bind_apply]
    rw [((IsExpr.addL _) _).1]
    have hsc := ((IsExpr.scale (-1) b) s).1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hsc]
    simp; ring
  | .atom f, s, hwf, hv => by
    simp only [NForm.Valid] at hv
    exact ⟨hwf, List.prefix_refl _, hv, by simp [NForm.encode, NForm.toFormula]⟩
  | .call P Q R w j, s, hwf, hv => by
    simp only [NForm.Valid] at hv
    exact ⟨hwf, List.prefix_refl _, hv.2.2.2, by simp [NForm.encode, NForm.toFormula]⟩
  | .and fs, s, hwf, hv => by
    simp only [NForm.Valid] at hv
    obtain ⟨h1, h2, h3, h4⟩ := encodeList_correct fs s hwf hv
    set s1 := (NForm.encodeList T fs s).2
    set es := (NForm.encodeList T fs s).1
    obtain ⟨k1, k2, k3, k4⟩ := seqM_square_correct es s1 h1 h3
    obtain ⟨l1, l2, l3⟩ := Triple.addL (T := T) (P := fun t => ∀ x ∈ (seqM (es.map square) s1).1,
      x.Valid T t) _ (fun _ h => h) _ k1 k3
    refine ⟨l1, h2.trans (k2.trans l2), l3, ?_⟩
    simp only [NForm.encode, NForm.toFormula, Formula.compile_and, NM.bind_apply]
    rw [((IsExpr.addL _) _).1, k4]
    have : (es.map fun e => e.poly * e.poly) = (es.map Ex.poly).map (fun p => p * p) := by
      rw [List.map_map]; rfl
    rw [this, h4, List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left fun φ _ => by simp [sq]
  | .or fs, s, hwf, hv => by
    simp only [NForm.Valid] at hv
    obtain ⟨h1, h2, h3, h4⟩ := encodeList_correct fs s hwf hv
    obtain ⟨l1, l2, l3⟩ := Triple.mulL (T := T) (P := fun t => ∀ x ∈ (NForm.encodeList T fs s).1,
      x.Valid T t) _ (fun _ h => h) _ h1 h3
    refine ⟨l1, h2.trans l2, l3, ?_⟩
    simp only [NForm.encode, NForm.toFormula, Formula.compile_or, NM.bind_apply]
    rw [((IsExpr.mulL _) _).1, h4, List.map_map]
    rfl

theorem encodeList_correct : ∀ (fs : List NForm) (s : State), NodesWF s.nodes →
    (∀ φ ∈ fs, φ.Valid T s) →
    NodesWF (NForm.encodeList T fs s).2.nodes ∧ s.nodes <+: (NForm.encodeList T fs s).2.nodes ∧
      (∀ e ∈ (NForm.encodeList T fs s).1, e.Valid T (NForm.encodeList T fs s).2) ∧
      (NForm.encodeList T fs s).1.map Ex.poly = fs.map fun φ => (φ.toFormula T).compile
  | [], s, hwf, _ => ⟨hwf, List.prefix_refl _, by simp [NForm.encodeList], by simp [NForm.encodeList]⟩
  | φ :: fs, s, hwf, hv => by
    obtain ⟨h1, h2, h3, h4⟩ := encode_correct φ s hwf (hv φ List.mem_cons_self)
    obtain ⟨k1, k2, k3, k4⟩ := encodeList_correct fs _ h1
      fun ψ hψ => (hv ψ (List.mem_cons_of_mem _ hψ)).mono T h2
    refine ⟨by simpa [NForm.encodeList] using k1, by simpa [NForm.encodeList] using h2.trans k2,
      ?_, ?_⟩
    · intro e he
      simp only [NForm.encodeList, NM.bind_apply, NM.pure_apply, List.mem_cons] at he ⊢
      rcases he with rfl | he
      · exact h3.mono T k2
      · exact k3 e he
    · simp only [NForm.encodeList, NM.bind_apply, NM.pure_apply, List.map_cons]
      rw [h4, k4]

end

end ZInQ.Compiler.Natural

namespace ZInQ.Compiler.Natural

open Syntax MvPolynomial

variable {T : ExPoly}

theorem init_nodesWF (k : ℕ) : NodesWF (State.init k).nodes := by
  intro j hj i hi
  simp [State.init, NatNode.children] at hi

theorem input_valid {k i : ℕ} (hi : i < k) : (⟨i, X i⟩ : Ex).Valid T (State.init k) := by
  have hl : i < (State.init k).nodes.length := by simp [State.init, hi]
  refine ⟨hl, ?_⟩
  simp only [State.vals]
  rw [getPoly_denoteNatNodes_of_wf T (init_nodesWF k) hl]
  simp [State.init, NatNode.denote]

/-! ### The node encoding does not depend on the call template -/

theorem addFrom_indep {acc acc' : Ex} {l l' : List Ex} (h : acc.node = acc'.node)
    (hl : l.map Ex.node = l'.map Ex.node) (s : State) :
    (addFrom acc l s).2 = (addFrom acc' l' s).2 ∧
      (addFrom acc l s).1.node = (addFrom acc' l' s).1.node := by
  induction l generalizing acc acc' l' s with
  | nil => cases l' with
    | nil => exact ⟨rfl, h⟩
    | cons _ _ => simp at hl
  | cons y ys ih => cases l' with
    | nil => simp at hl
    | cons y' ys' =>
      simp only [List.map_cons, List.cons.injEq] at hl
      simp only [addFrom, NM.bind_apply]
      rw [h, hl.1]
      exact ih (acc := ⟨_, acc.poly + y.poly⟩) (acc' := ⟨_, acc'.poly + y'.poly⟩) rfl hl.2 _

theorem mulFrom_indep {acc acc' : Ex} {l l' : List Ex} (h : acc.node = acc'.node)
    (hl : l.map Ex.node = l'.map Ex.node) (s : State) :
    (mulFrom acc l s).2 = (mulFrom acc' l' s).2 ∧
      (mulFrom acc l s).1.node = (mulFrom acc' l' s).1.node := by
  induction l generalizing acc acc' l' s with
  | nil => cases l' with
    | nil => exact ⟨rfl, h⟩
    | cons _ _ => simp at hl
  | cons y ys ih => cases l' with
    | nil => simp at hl
    | cons y' ys' =>
      simp only [List.map_cons, List.cons.injEq] at hl
      simp only [mulFrom, NM.bind_apply]
      rw [h, hl.1]
      exact ih (acc := ⟨_, acc.poly * y.poly⟩) (acc' := ⟨_, acc'.poly * y'.poly⟩) rfl hl.2 _

theorem addL_indep {l l' : List Ex} (hl : l.map Ex.node = l'.map Ex.node) (s : State) :
    (addL l s).2 = (addL l' s).2 ∧ (addL l s).1.node = (addL l' s).1.node := by
  cases l with
  | nil => cases l' with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ => simp at hl
  | cons x xs => cases l' with
    | nil => simp at hl
    | cons x' xs' =>
      simp only [List.map_cons, List.cons.injEq] at hl
      exact addFrom_indep hl.1 hl.2 s

theorem mulL_indep {l l' : List Ex} (hl : l.map Ex.node = l'.map Ex.node) (s : State) :
    (mulL l s).2 = (mulL l' s).2 ∧ (mulL l s).1.node = (mulL l' s).1.node := by
  cases l with
  | nil => cases l' with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ => simp at hl
  | cons x xs => cases l' with
    | nil => simp at hl
    | cons x' xs' =>
      simp only [List.map_cons, List.cons.injEq] at hl
      exact mulFrom_indep hl.1 hl.2 s

theorem seqM_square_indep {es es' : List Ex} (h : es.map Ex.node = es'.map Ex.node) (s : State) :
    (seqM (es.map square) s).2 = (seqM (es'.map square) s).2 ∧
      (seqM (es.map square) s).1.map Ex.node = (seqM (es'.map square) s).1.map Ex.node := by
  induction es generalizing es' s with
  | nil => cases es' with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ => simp at h
  | cons e es ih => cases es' with
    | nil => simp at h
    | cons e' es'' =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hsq := mulL_indep (l := [e, e]) (l' := [e', e']) (by simp [h.1]) s
      simp only [List.map_cons, seqM, NM.bind_apply, NM.pure_apply]
      have := ih h.2 (square e s).2
      rw [show (square e' s) = (mulL [e', e'] s) from rfl, ← hsq.1] at *
      refine ⟨this.1, ?_⟩
      simp only [List.cons.injEq]
      exact ⟨hsq.2, this.2⟩

/-- Induction on construction formulas with the hypothesis for every member of a conjunction or
a disjunction. -/
@[elab_as_elim]
theorem NForm.induct' {P : NForm → Prop} (eq : ∀ a b, P (.eq a b)) (atom : ∀ f, P (.atom f))
    (call : ∀ A B C w j, P (.call A B C w j)) (and : ∀ fs, (∀ φ ∈ fs, P φ) → P (.and fs))
    (or : ∀ fs, (∀ φ ∈ fs, P φ) → P (.or fs)) (φ : NForm) : P φ :=
  NForm.rec (motive_1 := P) (motive_2 := fun fs => ∀ φ ∈ fs, P φ) eq atom call and or
    (fun _ h => absurd h List.not_mem_nil)
    (fun _ _ hh ht => List.forall_mem_cons.2 ⟨hh, ht⟩) φ

theorem encodeList_indep_of (τ τ' : ExPoly) (fs : List NForm)
    (h : ∀ φ ∈ fs, ∀ s, (φ.encode τ s).2 = (φ.encode τ' s).2 ∧
      (φ.encode τ s).1.node = (φ.encode τ' s).1.node) (s : State) :
    (NForm.encodeList τ fs s).2 = (NForm.encodeList τ' fs s).2 ∧
      (NForm.encodeList τ fs s).1.map Ex.node = (NForm.encodeList τ' fs s).1.map Ex.node := by
  induction fs generalizing s with
  | nil => simp [NForm.encodeList]
  | cons φ fs ih =>
    simp only [NForm.encodeList, NM.bind_apply, NM.pure_apply, List.map_cons]
    have h1 := h φ List.mem_cons_self s
    rw [h1.1]
    have h2 := ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)) (φ.encode τ' s).2
    exact ⟨h2.1, by rw [h1.2, h2.2]⟩

theorem encode_indep (τ τ' : ExPoly) (φ : NForm) : ∀ s : State,
    (φ.encode τ s).2 = (φ.encode τ' s).2 ∧ (φ.encode τ s).1.node = (φ.encode τ' s).1.node := by
  induction φ using NForm.induct' with
  | eq a b => intro s; simp [NForm.encode]
  | atom f => intro s; simp [NForm.encode]
  | call A B C w j => intro s; simp [NForm.encode]
  | and fs ih =>
    intro s
    simp only [NForm.encode, NM.bind_apply]
    have h1 := encodeList_indep_of τ τ' fs ih s
    rw [h1.1]
    have h2 := seqM_square_indep h1.2 (NForm.encodeList τ' fs s).2
    rw [h2.1]
    exact addL_indep h2.2 _
  | or fs ih =>
    intro s
    simp only [NForm.encode, NM.bind_apply]
    have h1 := encodeList_indep_of τ τ' fs ih s
    rw [h1.1]
    exact mulL_indep h1.2 _

/-- **The polynomial of the natural circuit of a construction** is the compilation of its
formula, when the construction is valid from the initial state. -/
theorem toCircuit_poly {k : ℕ} {m : NM NForm} {P : State → Prop} (hP : P (State.init k))
    (hm : Triple P m fun φ s => φ.Valid T s) :
    (m.toCircuit k).poly T = (m.formula T k).compile := by
  obtain ⟨h1, -, h3⟩ := hm (State.init k) (init_nodesWF k) hP
  obtain ⟨-, -, k3, k4⟩ := encode_correct _ _ h1 h3
  have hind := encode_indep ExPoly.empty T (m (State.init k)).1 (m (State.init k)).2
  simp only [NatCircuit.poly, NM.formula, NM.toCircuit_nodes, NM.toCircuit_root, hind.1, hind.2]
  rw [← k4]
  exact k3.2

end ZInQ.Compiler.Natural
