import ZInQKernel.Compiler.NodeBound.Up

/-!
# Node bounds of the gadgets and macros (hierarchical mode)

For each gadget and macro, the numbers of addition and multiplication nodes it creates at most,
for all arguments and from every node list, and the encoding costs of its formula:

| macro | additions | multiplications | encoding |
|---|---|---|---|
| `lt` | 2 | 0 | (1, 1) |
| `odd` | 1 | 1 | (1, 1) |
| `power` | 0 | 0 | (0, 0) |
| `binomial` | 8 (7 if `N + 1` is present) | 2 | (8, 9) |
| `orthogonal` | 10 (9 if `a + b` is present) | 3 | (10, 12) |
| `mask` | 9 (8 if `b + 1` is present) | 3 | (10, 12) |
| `bitAnd` | 30 | 9 | (36, 43) |

The guaranteed internal repeat is subtracted in `bitAnd`: its orthogonalities `z ⊥ a` and
`z ⊥ b` re-request the sums `z + a` and `z + b` it has just built. "`N + 1` is present" is
`HasSucc N.node`: the node `N + 1` (with the node of the constant `1`) is in the node list.
-/

namespace ZInQ.Compiler.NodeBound

open Natural Universal

/-- The node `x + 1` is present (the constant `1` at its first index). -/
def HasSucc (x : ℕ) (l : List NatNode) : Prop :=
  ∃ o, l.idxOf? (.const 1) = some o ∧ NatNode.add x o ∈ l

theorem Mono.hasSucc (x : ℕ) : Mono (HasSucc x) := ⟨fun l l' h ⟨o, h1, h2⟩ =>
  ⟨o, (Mono.idxOf? _ _).mono l l' h h1, (Mono.mem _).mono l l' h h2⟩⟩

theorem HasSucc.mem {x e : ℕ} {l : List NatNode} (h : HasSucc x l)
    (he : l.idxOf? (.const 1) = some e) : NatNode.add x e ∈ l := by
  obtain ⟨o, h1, h2⟩ := h
  rw [h1, Option.some.injEq] at he
  exact he ▸ h2

theorem HasSucc.of_idxOf? {x e i : ℕ} {l : List NatNode} (he : l.idxOf? (.const 1) = some e)
    (h : l.idxOf? (.add x e) = some i) : HasSucc x l := ⟨e, he, mem_of_idxOf? h⟩

/-- Monotonicity side goals. -/
macro "up_mono" : tactic => `(tactic| first
  | (with_reducible apply Mono.and)
  | (with_reducible apply Mono.idxOf?)
  | (with_reducible apply Mono.mem)
  | (with_reducible apply Mono.hasSucc)
  | (with_reducible apply Mono.const)
  | (with_reducible apply Mono.imp)
  | (show Mono _; assumption))

/-- Presence side goals: a node present by a hypothesis. -/
macro "up_present" : tactic => `(tactic| (
  intro l h
  casesm* _ ∧ _
  first
  | assumption
  | exact mem_of_idxOf? (by assumption)
  | exact HasSucc.mem (by assumption) (by assumption)))

/-- One step of a bound proof. -/
macro "up_prim" : tactic => `(tactic| first
  | with_reducible exact Up.fresh
  | with_reducible exact Up.note _
  | with_reducible exact Up.constant _
  | with_reducible exact Up.callPower _ _ _
  | (with_reducible refine Up.node_hit ?_; up_present)
  | with_reducible exact Up.node_add _ _
  | with_reducible exact Up.node_mul _ _)

/-- A bind step. -/
macro "up_bind" : tactic => `(tactic| with_reducible apply Up.bind)

/-- Normalize the monad: flatten binds and drop `pure` steps. -/
macro "up_norm" : tactic => `(tactic| simp only [NM.bind_assoc', NM.pure_bind',
  ZInQ.Compiler.Natural.andM, ZInQ.Compiler.Natural.seqM.eq_1, ZInQ.Compiler.Natural.seqM.eq_2,
  ZInQ.Compiler.Natural.addL.eq_2, ZInQ.Compiler.Natural.addFrom.eq_1,
  ZInQ.Compiler.Natural.addFrom.eq_2, ZInQ.Compiler.Natural.mulL.eq_2,
  ZInQ.Compiler.Natural.mulFrom.eq_1, ZInQ.Compiler.Natural.mulFrom.eq_2,
  ZInQ.Compiler.Natural.square, ZInQ.Compiler.Natural.scale])

theorem Up.cost_of {α : Type} {P : List NatNode → Prop} {m : NM α} {a b a' b' : ℕ}
    {Q : α → List NatNode → Prop} (h : Up P m a b Q) (ha : a = a') (hb : b = b') :
    Up P m a' b' Q := ha ▸ hb ▸ h

theorem HasSucc.of_idxOf?' {x e i : ℕ} {l : List NatNode} (h : l.idxOf? (.add x e) = some i)
    (he : l.idxOf? (.const 1) = some e) : HasSucc x l := ⟨e, he, mem_of_idxOf? h⟩

/-- The final step: the postcondition from the accumulated facts. -/
macro "up_fin" : tactic => `(tactic| (with_reducible apply Up.pure; intro l h; casesm* _ ∧ _, Cost _ _ _, CostL _ _ _ _))

/-- A bound proof: binds, primitives, the extra steps `t`, and the final step. -/
macro "up_run" t:tacticSeq : tactic => `(tactic| repeat' (first
  | ($t)
  | up_bind
  | (intro _)
  | up_mono
  | up_prim
  | up_fin))

/-- A bound proof without extra steps. -/
macro "up_run0" : tactic => `(tactic| up_run fail)

/-- Encoding costs from the accumulated facts. -/
macro "up_costs" : tactic => `(tactic| first
  | (exact ⟨by simp only [encA, encAL, List.length_cons, List.length_nil, *],
      by simp only [encM, encML, List.length_cons, List.length_nil, *]⟩)
  | (exact ⟨by simp only [encA, encAL, List.length_cons, List.length_nil, *],
      by simp only [encM, encML, List.length_cons, List.length_nil, *],
      by simp only [List.length_cons, List.length_nil]⟩))

variable {P : List NatNode → Prop}

theorem lt_up (hP : Mono P) (a b : Ex) : Up P (Natural.lt a b) 2 0 (fun φ _ => Cost 1 1 φ) := by
  apply Up.cost_of
  case h =>
    unfold Natural.lt
    up_norm
    up_run0
    all_goals exact ⟨rfl, rfl⟩
  all_goals rfl

theorem odd_up (hP : Mono P) (x : Ex) : Up P (Natural.odd x) 1 1 (fun φ _ => Cost 1 1 φ) := by
  apply Up.cost_of
  case h =>
    unfold Natural.odd
    up_norm
    up_run0
    all_goals exact ⟨rfl, rfl⟩
  all_goals rfl

theorem power_up (hP : Mono P) (A B C : Ex) :
    Up P (Natural.power .hierarchical A B C) 0 0 (fun φ _ => Cost 0 0 φ) := by
  apply Up.cost_of
  case h =>
    unfold Natural.power
    up_norm
    up_run0
  all_goals rfl

/-- One step through a sub-macro. -/
macro "up_lt" : tactic => `(tactic| first
  | with_reducible refine lt_up ?_ _ _
  | with_reducible refine odd_up ?_ _
  | with_reducible refine power_up ?_ _ _ _)


theorem binomial_up (hP : Mono P) (C N K : Ex) :
    Up P (Natural.binomial .hierarchical C N K) 8 2
      (fun φ l => Cost 8 9 φ ∧ HasSucc N.node l) := by
  apply Up.cost_of
  case h =>
    unfold Natural.binomial
    up_norm
    up_run up_lt
    all_goals refine ⟨?_, HasSucc.of_idxOf?' (x := N.node) (by assumption) (by assumption)⟩
    all_goals up_costs
  all_goals rfl

theorem binomial_up_succ (hP : Mono P) (C N K : Ex) (hN : ∀ l, P l → HasSucc N.node l) :
    Up P (Natural.binomial .hierarchical C N K) 7 2 (fun φ _ => Cost 8 9 φ) := by
  refine Up.pre (P := fun l => P l ∧ HasSucc N.node l) ?_ fun l hl => ⟨hl, hN l hl⟩
  apply Up.cost_of
  case h =>
    unfold Natural.binomial
    up_norm
    up_run up_lt
    all_goals up_costs
  all_goals rfl

/-- One step through `binomial`. -/
macro "up_binomial" : tactic => `(tactic| first
  | (with_reducible refine binomial_up_succ ?_ _ _ _ ?_; rotate_left; up_present)
  | with_reducible refine binomial_up ?_ _ _ _)

theorem orthogonal_up (hP : Mono P) (a b : Ex) :
    Up P (Natural.orthogonal .hierarchical a b) 10 3 (fun φ _ => Cost 10 12 φ) := by
  apply Up.cost_of
  case h =>
    unfold Natural.orthogonal
    up_norm
    up_run first | up_lt | up_binomial
    all_goals up_costs
  all_goals rfl

theorem orthogonal_up_hit (hP : Mono P) (a b : Ex) (hab : ∀ l, P l → .add a.node b.node ∈ l) :
    Up P (Natural.orthogonal .hierarchical a b) 9 3 (fun φ _ => Cost 10 12 φ) := by
  refine Up.pre (P := fun l => P l ∧ .add a.node b.node ∈ l) ?_ fun l hl => ⟨hl, hab l hl⟩
  apply Up.cost_of
  case h =>
    unfold Natural.orthogonal
    up_norm
    up_run first | up_lt | up_binomial
    all_goals up_costs
  all_goals rfl

theorem mask_up (hP : Mono P) (a b : Ex) :
    Up P (Natural.mask .hierarchical a b) 9 3 (fun φ l => Cost 10 12 φ ∧ HasSucc b.node l) := by
  apply Up.cost_of
  case h =>
    unfold Natural.mask
    up_norm
    up_run first | up_lt | up_binomial
    all_goals exact ⟨by up_costs, by assumption⟩
  all_goals rfl

theorem mask_up_succ (hP : Mono P) (a b : Ex) (hb : ∀ l, P l → HasSucc b.node l) :
    Up P (Natural.mask .hierarchical a b) 8 3 (fun φ l => Cost 10 12 φ ∧ HasSucc b.node l) := by
  refine Up.pre (P := fun l => P l ∧ HasSucc b.node l) ?_ fun l hl => ⟨hl, hb l hl⟩
  apply Up.cost_of
  case h =>
    unfold Natural.mask
    up_norm
    up_run first | up_lt | up_binomial
    all_goals exact ⟨by up_costs, by assumption⟩
  all_goals rfl

/-- One step through `orthogonal`. -/
macro "up_orthogonal" : tactic => `(tactic| first
  | (with_reducible refine orthogonal_up_hit ?_ _ _ ?_; rotate_left; up_present)
  | with_reducible refine orthogonal_up ?_ _ _)

theorem bitAnd_up (hP : Mono P) (z x y : Ex) :
    Up P (Natural.bitAnd .hierarchical z x y) 30 9 (fun φ _ => Cost 36 43 φ) := by
  apply Up.cost_of
  case h =>
    unfold Natural.bitAnd
    up_norm
    up_run up_orthogonal
    all_goals up_costs
  all_goals rfl

end ZInQ.Compiler.NodeBound
