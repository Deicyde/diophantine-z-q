import ZInQKernel.Compiler.Translation.Soundness
import ZInQKernel.Syntax.Recipes.Translate

/-!
# The translation has the shape used by the semantics

`Syntax.translate` (syntax chapter) builds a model-evaluation recipe by one allocation counter.
Running it alongside a record of its allocations (`Alloc`: the fresh points with their
identities and the blocks) shows that, for a well-formed circuit, its output has the shape
`TranslationShape` used by soundness and completeness (`translateShape`): point references of
the explicit variables and nodes, rows, constant definitions and operations, and fresh points
that are pairwise disjoint because the counter only grows.
-/

namespace ZInQ.Translation

open Compiler.Natural Syntax

/-! ### Folds with a record -/

theorem foldl_pair_fst {α σ β : Type*} (f : σ → α → σ) (g : σ → β → α → β) (l : List α)
    (s : σ) (b : β) :
    (l.foldl (fun sb a => (f sb.1 a, g sb.1 sb.2 a)) (s, b)).1 = l.foldl f s := by
  induction l generalizing s b with
  | nil => rfl
  | cons a l ih => exact ih _ _

theorem foldl_pair_append {α σ β : Type*} (f : σ → α → σ) (g : σ → β → α → β) (l : List α)
    (a : α) (sb : σ × β) :
    (l ++ [a]).foldl (fun sb a => (f sb.1 a, g sb.1 sb.2 a)) sb =
      (f (l.foldl (fun sb a => (f sb.1 a, g sb.1 sb.2 a)) sb).1 a,
        g (l.foldl (fun sb a => (f sb.1 a, g sb.1 sb.2 a)) sb).1
          (l.foldl (fun sb a => (f sb.1 a, g sb.1 sb.2 a)) sb).2 a) := by
  simp [List.foldl_append]

/-! ### Allocation records -/

/-- The allocations of a translation run: fresh points with their identities, and blocks
`(start, length)`. -/
structure Alloc where
  slots : List (ℕ × Slot)
  blocks : List (ℕ × ℕ)

/-- The intervals `[a, a + m)` and `[b, b + n)` are disjoint. -/
def IntervalDisjoint (a m b n : ℕ) : Prop := a + m ≤ b ∨ b + n ≤ a

/-- The allocations lie in `[p + 3, n)` and are pairwise disjoint. -/
structure AllocInv (p n : ℕ) (al : Alloc) : Prop where
  slot_range : ∀ e ∈ al.slots, p + 3 ≤ e.1 ∧ e.1 + 5 ≤ n
  block_range : ∀ b ∈ al.blocks, p + 3 ≤ b.1 ∧ b.1 + b.2 ≤ n
  slots_sep : al.slots.Pairwise fun e e' => Separated e.1 e'.1
  blocks_disj : al.blocks.Pairwise fun b b' => IntervalDisjoint b.1 b.2 b'.1 b'.2
  slot_block : ∀ e ∈ al.slots, ∀ b ∈ al.blocks, IntervalDisjoint e.1 5 b.1 b.2

theorem AllocInv.nil (p n : ℕ) : AllocInv p n ⟨[], []⟩ :=
  ⟨by simp, by simp, List.Pairwise.nil, List.Pairwise.nil, by simp⟩

theorem AllocInv.mono {p n n' : ℕ} {al : Alloc} (h : AllocInv p n al) (hn : n ≤ n') :
    AllocInv p n' al :=
  ⟨fun e he => ⟨(h.slot_range e he).1, by have := (h.slot_range e he).2; omega⟩,
    fun b hb => ⟨(h.block_range b hb).1, by have := (h.block_range b hb).2; omega⟩,
    h.slots_sep, h.blocks_disj, h.slot_block⟩

theorem AllocInv.addSlot {p n : ℕ} {al : Alloc} (h : AllocInv p n al) (hp : p + 3 ≤ n)
    (sl : Slot) : AllocInv p (n + 5) ⟨al.slots ++ [(n, sl)], al.blocks⟩ := by
  refine ⟨fun e he => ?_, fun b hb => ?_, ?_, h.blocks_disj, fun e he b hb => ?_⟩
  · rcases List.mem_append.1 he with he | he
    · have := h.slot_range e he; omega
    · rw [List.mem_singleton] at he; subst he; simp; omega
  · have := h.block_range b hb; omega
  · refine List.pairwise_append.2 ⟨h.slots_sep, List.pairwise_singleton _ _, fun e he e' he' => ?_⟩
    rw [List.mem_singleton] at he'; subst he'
    have := h.slot_range e he
    left; simp only; omega
  · rcases List.mem_append.1 he with he | he
    · exact h.slot_block e he b hb
    · rw [List.mem_singleton] at he; subst he
      have := h.block_range b hb
      right; simp only; omega

theorem AllocInv.addBlock {p n : ℕ} {al : Alloc} (h : AllocInv p n al) (hp : p + 3 ≤ n)
    (len : ℕ) : AllocInv p (n + len) ⟨al.slots, al.blocks ++ [(n, len)]⟩ := by
  refine ⟨fun e he => ?_, fun b hb => ?_, h.slots_sep, ?_, fun e he b hb => ?_⟩
  · have := h.slot_range e he; omega
  · rcases List.mem_append.1 hb with hb | hb
    · have := h.block_range b hb; omega
    · rw [List.mem_singleton] at hb; subst hb; simp; omega
  · refine List.pairwise_append.2 ⟨h.blocks_disj, List.pairwise_singleton _ _,
      fun b hb b' hb' => ?_⟩
    rw [List.mem_singleton] at hb'; subst hb'
    have := h.block_range b hb
    left; simp only; omega
  · rcases List.mem_append.1 hb with hb | hb
    · exact h.slot_block e he b hb
    · rw [List.mem_singleton] at hb; subst hb
      have := h.slot_range e he
      left; simp only; omega

/-! ### The variable stage -/

/-- The natural flag of an explicit variable: a natural block is taken. -/
def natFlag (k : ℕ) (natIn : Bool) (v : ℕ × VarKind) : Bool := !(decide (IsInputVar k v)) || natIn

/-- The allocations of one explicit variable. -/
def allocVar (k : ℕ) (natIn : Bool) (s : TrState) (al : Alloc) (v : ℕ × VarKind) : Alloc :=
  ⟨al.slots ++ (if IsInputVar k v then [] else [(s.next, Slot.var v.1)]),
    al.blocks ++ (if natFlag k natIn v then
      [(if IsInputVar k v then s.next else s.next + 5, 140604)] else [])⟩

/-- The natural block of a source row. -/
def natBlk (row : ℤ × Option ℕ) : Option (ℕ × ℕ) := row.2.map fun st => (st, 140604)

/-- The invariant of the variable stage after the explicit variables `l`. -/
structure VarInv (k : ℕ) (natIn : Bool) (p : ℕ) (l : List (ℕ × VarKind)) (s : TrState)
    (al : Alloc) : Prop where
  next_ge : p + 3 ≤ s.next
  alloc : AllocInv p s.next al
  nodePts : s.nodePts = []
  constRefs : s.constRefs = []
  constants : s.constants = []
  operations : s.operations = []
  keys : s.varRefs.map Prod.fst = l.map Prod.fst
  var : ∀ v ∈ l, ∃ r, (v.1, r) ∈ s.varRefs ∧ (IsInputVar k v → r = 5 * v.1) ∧
    (¬ IsInputVar k v → ∃ q : ℕ, r = q ∧ (q, Slot.var v.1) ∈ al.slots) ∧
    (natFlag k natIn v = true → ∃ st, (r, some st) ∈ s.sources ∧ (st, 140604) ∈ al.blocks)
  row : ∀ row ∈ s.sources, ∃ v ∈ l, (v.1, row.1) ∈ s.varRefs ∧
    (∀ st, row.2 = some st → natFlag k natIn v = true ∧ (st, 140604) ∈ al.blocks)
  natBlocks : s.sources.filterMap natBlk = al.blocks

theorem trVar_input {k : ℕ} {natIn : Bool} {s : TrState} {v : ℕ × VarKind}
    (hI : IsInputVar k v) :
    trVar k natIn s v = { s with
      next := if natIn then s.next + 140604 else s.next
      varRefs := s.varRefs ++ [(v.1, 5 * (v.1 : ℤ))]
      sources := s.sources ++ [(5 * (v.1 : ℤ), if natIn then some s.next else none)] } := by
  cases natIn <;> simp [trVar, hI]

theorem trVar_witness {k : ℕ} {natIn : Bool} {s : TrState} {v : ℕ × VarKind}
    (hI : ¬ IsInputVar k v) :
    trVar k natIn s v = { s with
      next := s.next + 5 + 140604
      varRefs := s.varRefs ++ [(v.1, (s.next : ℤ))]
      sources := s.sources ++ [((s.next : ℤ), some (s.next + 5))] } := by
  simp [trVar, hI]

theorem allocVar_input {k : ℕ} {natIn : Bool} {s : TrState} {al : Alloc} {v : ℕ × VarKind}
    (hI : IsInputVar k v) :
    allocVar k natIn s al v =
      ⟨al.slots, al.blocks ++ (if natIn then [(s.next, 140604)] else [])⟩ := by
  cases natIn <;> simp [allocVar, natFlag, hI]

theorem allocVar_witness {k : ℕ} {natIn : Bool} {s : TrState} {al : Alloc} {v : ℕ × VarKind}
    (hI : ¬ IsInputVar k v) :
    allocVar k natIn s al v =
      ⟨al.slots ++ [(s.next, Slot.var v.1)], al.blocks ++ [(s.next + 5, 140604)]⟩ := by
  simp [allocVar, natFlag, hI]

theorem varInv_step {k : ℕ} {natIn : Bool} {p : ℕ} {l : List (ℕ × VarKind)} {s : TrState}
    {al : Alloc} (h : VarInv k natIn p l s al) (v : ℕ × VarKind) :
    VarInv k natIn p (l ++ [v]) (trVar k natIn s v) (allocVar k natIn s al v) := by
  have hal := h.alloc
  by_cases hI : IsInputVar k v
  · have hnf : natFlag k natIn v = natIn := by simp [natFlag, hI]
    rw [trVar_input hI, allocVar_input hI]
    refine ⟨?_, ?_, h.nodePts, h.constRefs, h.constants, h.operations, by simp [h.keys], ?_, ?_,
      ?_⟩
    · have := h.next_ge; dsimp only; split_ifs <;> omega
    · cases natIn
      · simpa using hal
      · simpa using hal.addBlock h.next_ge 140604
    · intro v' hv'
      rcases List.mem_append.1 hv' with hv' | hv'
      · obtain ⟨r, hr, h1, h2, h3⟩ := h.var v' hv'
        refine ⟨r, by simp [hr], h1, fun hn => ?_, fun hn => ?_⟩
        · obtain ⟨q, hq, hs⟩ := h2 hn
          exact ⟨q, hq, hs⟩
        · obtain ⟨st, hst, hb⟩ := h3 hn
          exact ⟨st, by simp [hst], by simp [hb]⟩
      · rw [List.mem_singleton] at hv'; subst hv'
        refine ⟨5 * v'.1, by simp, fun _ => rfl, fun h' => absurd hI h', fun hn => ?_⟩
        rw [hnf] at hn; subst hn
        exact ⟨s.next, by simp, by simp⟩
    · intro row hrow
      simp only [List.mem_append, List.mem_singleton] at hrow
      rcases hrow with hrow | rfl
      · obtain ⟨v', hv', hr, hst⟩ := h.row row hrow
        refine ⟨v', List.mem_append_left _ hv', by simp [hr], fun st hs => ?_⟩
        obtain ⟨h1, h2⟩ := hst st hs
        exact ⟨h1, by simp [h2]⟩
      · refine ⟨v, by simp, by simp, fun st hs => ?_⟩
        cases natIn
        · simp at hs
        · simp only [ite_true, Option.some.injEq] at hs
          subst hs
          exact ⟨hnf, by simp⟩
    · rw [List.filterMap_append, h.natBlocks]
      cases natIn <;> simp [natBlk]
  · have hnf : natFlag k natIn v = true := by simp [natFlag, hI]
    rw [trVar_witness hI, allocVar_witness hI]
    refine ⟨by have := h.next_ge; show p + 3 ≤ s.next + 5 + 140604; omega, ?_, h.nodePts,
      h.constRefs, h.constants, h.operations, by simp [h.keys], ?_, ?_, ?_⟩
    · have h1 := hal.addSlot h.next_ge (Slot.var v.1)
      have h2 := h1.addBlock (by have := h.next_ge; omega) 140604
      exact h2
    · intro v' hv'
      rcases List.mem_append.1 hv' with hv' | hv'
      · obtain ⟨r, hr, h1, h2, h3⟩ := h.var v' hv'
        refine ⟨r, by simp [hr], h1, fun hn => ?_, fun hn => ?_⟩
        · obtain ⟨q, hq, hs⟩ := h2 hn
          exact ⟨q, hq, by simp [hs]⟩
        · obtain ⟨st, hst, hb⟩ := h3 hn
          exact ⟨st, by simp [hst], by simp [hb]⟩
      · rw [List.mem_singleton] at hv'; subst hv'
        exact ⟨s.next, by simp, fun h' => absurd h' hI, fun _ => ⟨s.next, rfl, by simp⟩,
          fun _ => ⟨s.next + 5, by simp, by simp⟩⟩
    · intro row hrow
      simp only [List.mem_append, List.mem_singleton] at hrow
      rcases hrow with hrow | rfl
      · obtain ⟨v', hv', hr, hst⟩ := h.row row hrow
        refine ⟨v', List.mem_append_left _ hv', by simp [hr], fun st hs => ?_⟩
        obtain ⟨h1, h2⟩ := hst st hs
        exact ⟨h1, by simp [h2]⟩
      · refine ⟨v, by simp, by simp, fun st hs => ?_⟩
        simp only [Option.some.injEq] at hs
        subst hs
        exact ⟨hnf, by simp⟩
    · rw [List.filterMap_append, h.natBlocks]
      simp [natBlk]

/-- The initial state of the variable stage: the counter after the parameters and the
generator variables. -/
def trInit (p : ℕ) : TrState := ⟨p + 3, [], [], [], [], [], []⟩

theorem varInv_foldl (k : ℕ) (natIn : Bool) (p : ℕ) (l : List (ℕ × VarKind)) :
    VarInv k natIn p l
      (l.foldl (fun sa v => (trVar k natIn sa.1 v, allocVar k natIn sa.1 sa.2 v))
        (trInit p, ⟨[], []⟩)).1
      (l.foldl (fun sa v => (trVar k natIn sa.1 v, allocVar k natIn sa.1 sa.2 v))
        (trInit p, ⟨[], []⟩)).2 := by
  induction l using List.reverseRecOn with
  | nil =>
    exact ⟨le_rfl, AllocInv.nil _ _, rfl, rfl, rfl, rfl, rfl, by simp, by simp [trInit], rfl⟩
  | append_singleton l v ih =>
    rw [foldl_pair_append]
    exact varInv_step ih v

/-! ### The node stage -/

/-- The block length of an operation node. -/
def opLen (powerW : ℕ) : NatNode → ℕ
  | .add _ _ => 6
  | .mul _ _ => 35134
  | .call _ _ _ _ => powerW
  | _ => 0

/-- Addition, multiplication and call nodes. -/
def IsOpNode : NatNode → Prop
  | .add _ _ => True
  | .mul _ _ => True
  | .call _ _ _ _ => True
  | _ => False

/-- The operation of an operation node with output point `q`, the arguments read from `pts`. -/
def opFor (pts : List ℤ) (q : ℕ) : NatNode → Operation
  | .add a b => .add (pts.getD a (-4)) (pts.getD b (-4)) q (q + 5)
  | .mul a b => .mul (pts.getD a (-4)) (pts.getD b (-4)) q (q + 5)
  | .call a b c _ => .power (pts.getD a (-4)) (pts.getD b (-4)) (pts.getD c (-4)) q (q + 5)
  | _ => .add 0 0 0 0

theorem opFor_append {pts : List ℤ} (x : ℤ) (q : ℕ) {n : NatNode}
    (h : ∀ a ∈ n.children, a < pts.length) : opFor (pts ++ [x]) q n = opFor pts q n := by
  cases n <;> simp_all [opFor, NatNode.children, List.getElem?_append_left]

/-- The allocations of one node. -/
def allocNode (powerW : ℕ) (s : TrState) (al : Alloc) : NatNode → Alloc
  | .var _ => al
  | .const c => if IsNontrivial c ∧ assocLookup s.constRefs c = none then
      ⟨al.slots ++ [(s.next, Slot.const c)], al.blocks ++ [(s.next + 5, 1)]⟩ else al
  | n => ⟨al.slots ++ [(s.next, Slot.node s.nodePts.length)], al.blocks ++ [(s.next + 5, opLen powerW n)]⟩

/-- The block of a constant definition. -/
def constBlk (d : ℕ × ℤ × ℕ) : ℕ × ℕ := (d.2.2, 1)

/-- The block of an operation. -/
def opBlk (powerW : ℕ) : Operation → ℕ × ℕ
  | .add _ _ _ s => (s, 6)
  | .mul _ _ _ s => (s, 35134)
  | .power _ _ _ _ s => (s, powerW)

/-- The call blocks of the recipe, in the order of its conjuncts. -/
def formulaBlocks (powerW : ℕ) (s : TrState) : List (ℕ × ℕ) :=
  s.sources.filterMap natBlk ++ s.constants.map constBlk ++ s.operations.map (opBlk powerW)

theorem opBlk_opFor (powerW : ℕ) (pts : List ℤ) (q : ℕ) {n : NatNode} (hn : IsOpNode n) :
    opBlk powerW (opFor pts q n) = (q + 5, opLen powerW n) := by
  cases n <;> simp only [IsOpNode] at hn <;> rfl

/-- The point of node `j` and what it records. -/
def NodePt (consts : List ℤ) (s : TrState) (al : Alloc) (j : ℕ) (pj : ℤ) : NatNode → Prop
  | .var i => pj = (assocLookup s.varRefs i).getD (-4)
  | .const c => (IsNontrivial c → ∃ q : ℕ, pj = q ∧ (q, Slot.const c) ∈ al.slots ∧
      (18 + consts.idxOf c, (q : ℤ), q + 5) ∈ s.constants) ∧ (¬ IsNontrivial c → pj = trivialRef c)
  | n => ∃ q : ℕ, pj = q ∧ (q, Slot.node j) ∈ al.slots ∧ opFor s.nodePts q n ∈ s.operations

/-- The invariant of the node stage after the nodes `l`, from the state `sV`, `alV` after the
variable stage. -/
structure NodeInv (consts : List ℤ) (powerW p : ℕ) (sV : TrState) (alV : Alloc)
    (l : List NatNode) (s : TrState) (al : Alloc) : Prop where
  next_ge : p + 3 ≤ s.next
  alloc : AllocInv p s.next al
  varRefs : s.varRefs = sV.varRefs
  sources : s.sources = sV.sources
  slots_sub : ∀ e ∈ alV.slots, e ∈ al.slots
  blocks_sub : ∀ b ∈ alV.blocks, b ∈ al.blocks
  len : s.nodePts.length = l.length
  pt : ∀ (j : ℕ) (n : NatNode) (pj : ℤ), l[j]? = some n → s.nodePts[j]? = some pj → NodePt consts s al j pj n
  constRefs : ∀ e ∈ s.constRefs, IsNontrivial e.1 ∧ ∃ q : ℕ, e.2 = q ∧
    (q, Slot.const e.1) ∈ al.slots ∧ (18 + consts.idxOf e.1, (q : ℤ), q + 5) ∈ s.constants ∧
    ∃ j : ℕ, l[j]? = some (NatNode.const e.1) ∧ s.nodePts[j]? = some e.2
  constants : ∀ d ∈ s.constants, (∃ e ∈ s.constRefs, ∃ q : ℕ, e.2 = q ∧
    d = (18 + consts.idxOf e.1, (q : ℤ), q + 5)) ∧ (d.2.2, 1) ∈ al.blocks
  ops : ∀ op ∈ s.operations, ∃ (j : ℕ) (n : NatNode), ∃ q : ℕ, l[j]? = some n ∧ s.nodePts[j]? = some (q : ℤ) ∧
    IsOpNode n ∧ op = opFor s.nodePts q n ∧ (q + 5, opLen powerW n) ∈ al.blocks
  perm : (formulaBlocks powerW s).Perm al.blocks

theorem NodePt.mono {consts : List ℤ} {s s' : TrState} {al al' : Alloc} {j : ℕ} {pj : ℤ}
    {n : NatNode} (h : NodePt consts s al j pj n) (hv : s'.varRefs = s.varRefs)
    (hsl : ∀ e ∈ al.slots, e ∈ al'.slots) (hc : ∀ d ∈ s.constants, d ∈ s'.constants)
    (ho : ∀ op ∈ s.operations, op ∈ s'.operations)
    (hop : ∀ q, opFor s'.nodePts q n = opFor s.nodePts q n) : NodePt consts s' al' j pj n := by
  cases n with
  | var i => simp only [NodePt] at h ⊢; rw [hv]; exact h
  | const c =>
    simp only [NodePt] at h ⊢
    refine ⟨fun hc' => ?_, h.2⟩
    obtain ⟨q, hq, h1, h2⟩ := h.1 hc'
    exact ⟨q, hq, hsl _ h1, hc _ h2⟩
  | add a b =>
    simp only [NodePt] at h ⊢
    obtain ⟨q, hq, h1, h2⟩ := h
    exact ⟨q, hq, hsl _ h1, by rw [hop]; exact ho _ h2⟩
  | mul a b =>
    simp only [NodePt] at h ⊢
    obtain ⟨q, hq, h1, h2⟩ := h
    exact ⟨q, hq, hsl _ h1, by rw [hop]; exact ho _ h2⟩
  | call a b c w =>
    simp only [NodePt] at h ⊢
    obtain ⟨q, hq, h1, h2⟩ := h
    exact ⟨q, hq, hsl _ h1, by rw [hop]; exact ho _ h2⟩

theorem trNode_op (consts : List ℤ) (powerW : ℕ) (s : TrState) {n : NatNode} (hn : IsOpNode n) :
    trNode consts powerW s n = { s with
      next := s.next + 5 + opLen powerW n
      nodePts := s.nodePts ++ [(s.next : ℤ)]
      operations := s.operations ++ [opFor s.nodePts s.next n] } := by
  cases n <;> simp only [IsOpNode] at hn <;> rfl

theorem allocNode_op (powerW : ℕ) (s : TrState) (al : Alloc) {n : NatNode} (hn : IsOpNode n) :
    allocNode powerW s al n = ⟨al.slots ++ [(s.next, Slot.node s.nodePts.length)],
      al.blocks ++ [(s.next + 5, opLen powerW n)]⟩ := by
  cases n <;> simp only [IsOpNode] at hn <;> rfl

theorem lt_of_getElem? {α : Type*} {l : List α} {j : ℕ} {y : α} (h : l[j]? = some y) :
    j < l.length :=
  (List.getElem?_eq_some_iff.1 h).1

theorem getElem?_append_old {α : Type*} {l : List α} {x : α} {j : ℕ} {y : α}
    (h : l[j]? = some y) : (l ++ [x])[j]? = some y := by
  rw [List.getElem?_append_left (lt_of_getElem? h)]; exact h

theorem getElem?_append_new {α : Type*} {l : List α} {x : α} {j : ℕ} {y : α}
    (h : (l ++ [x])[j]? = some y) : l[j]? = some y ∨ (j = l.length ∧ y = x) := by
  rcases Nat.lt_or_ge j l.length with hj | hj
  · left; rwa [List.getElem?_append_left hj] at h
  · right
    rw [List.getElem?_append_right hj] at h
    rcases hjl : j - l.length with _ | m
    · rw [hjl] at h; simp at h; exact ⟨by omega, h.symm⟩
    · rw [hjl] at h; simp at h

/-- The facts common to all node steps: the new point is appended, old entries keep their
facts. -/
theorem nodeInv_step_of {consts : List ℤ} {powerW p : ℕ} {sV : TrState} {alV : Alloc}
    {l : List NatNode} {s : TrState} {al : Alloc} (h : NodeInv consts powerW p sV alV l s al)
    (hwfl : ∀ (j : ℕ) (n' : NatNode), l[j]? = some n' → ∀ a ∈ n'.children, a < j)
    (n : NatNode) (s' : TrState) (al' : Alloc) (x : ℤ)
    (hnext : p + 3 ≤ s'.next) (hal : AllocInv p s'.next al')
    (hpts : s'.nodePts = s.nodePts ++ [x]) (hv : s'.varRefs = s.varRefs)
    (hsrc : s'.sources = s.sources)
    (hsl : ∀ e ∈ al.slots, e ∈ al'.slots) (hbl : ∀ b ∈ al.blocks, b ∈ al'.blocks)
    (hcs : ∀ d ∈ s.constants, d ∈ s'.constants) (hos : ∀ op ∈ s.operations, op ∈ s'.operations)
    (hnew : NodePt consts s' al' l.length x n)
    (hcr : ∀ e ∈ s'.constRefs, e ∈ s.constRefs ∨ (IsNontrivial e.1 ∧ ∃ q : ℕ, e.2 = q ∧
      (q, Slot.const e.1) ∈ al'.slots ∧ (18 + consts.idxOf e.1, (q : ℤ), q + 5) ∈ s'.constants ∧
      n = .const e.1 ∧ x = e.2))
    (hcd : ∀ d ∈ s'.constants, d ∈ s.constants ∨ ((∃ e ∈ s'.constRefs, ∃ q : ℕ, e.2 = q ∧
      d = (18 + consts.idxOf e.1, (q : ℤ), q + 5)) ∧ (d.2.2, 1) ∈ al'.blocks))
    (hcr_sub : ∀ e ∈ s.constRefs, e ∈ s'.constRefs)
    (hod : ∀ op ∈ s'.operations, op ∈ s.operations ∨ ∃ q : ℕ, x = q ∧ IsOpNode n ∧
      op = opFor s'.nodePts q n ∧ (q + 5, opLen powerW n) ∈ al'.blocks)
    (hperm : (formulaBlocks powerW s').Perm al'.blocks) :
    NodeInv consts powerW p sV alV (l ++ [n]) s' al' := by
  have hlen := h.len
  have oldOp : ∀ (q : ℕ) (n' : NatNode) (j : ℕ), l[j]? = some n' →
      opFor s'.nodePts q n' = opFor s.nodePts q n' := by
    intro q n' j hj
    rw [hpts]
    refine opFor_append x q fun a ha => ?_
    have := hwfl j n' hj a ha
    have := lt_of_getElem? hj
    omega
  refine ⟨hnext, hal, hv.trans h.varRefs, hsrc.trans h.sources, fun e he => hsl _ (h.slots_sub e he),
    fun b hb => hbl _ (h.blocks_sub b hb), by simp [hpts, hlen], ?_, ?_, ?_, ?_, hperm⟩
  · intro j n' pj hj hp
    rw [hpts] at hp
    rcases getElem?_append_new hj with hj' | ⟨rfl, rfl⟩
    · have hp' : s.nodePts[j]? = some pj := by
        rcases getElem?_append_new hp with hp' | ⟨hjl, -⟩
        · exact hp'
        · have := lt_of_getElem? hj'; omega
      exact (h.pt j n' pj hj' hp').mono hv hsl hcs hos fun q => oldOp q n' j hj'
    · rcases getElem?_append_new hp with hp' | ⟨-, rfl⟩
      · have := lt_of_getElem? hp'; omega
      · exact hnew
  · intro e he
    rcases hcr e he with he' | ⟨hn, q, hq, h1, h2, rfl, rfl⟩
    · obtain ⟨hn, q, hq, h1, h2, j, hj, hp⟩ := h.constRefs e he'
      exact ⟨hn, q, hq, hsl _ h1, hcs _ h2, j, getElem?_append_old hj,
        by rw [hpts]; exact getElem?_append_old hp⟩
    · exact ⟨hn, q, hq, h1, h2, l.length, by simp, by simp [hpts, hlen]⟩
  · intro d hd
    rcases hcd d hd with hd' | hd'
    · obtain ⟨⟨e, he, q, hq, rfl⟩, hb⟩ := h.constants d hd'
      exact ⟨⟨e, hcr_sub e he, q, hq, rfl⟩, hbl _ hb⟩
    · exact hd'
  · intro op hop'
    rcases hod op hop' with hop' | ⟨q, rfl, hn, rfl, hb⟩
    · obtain ⟨j, n', q, hj, hp, hn', rfl, hb⟩ := h.ops op hop'
      exact ⟨j, n', q, getElem?_append_old hj, by rw [hpts]; exact getElem?_append_old hp, hn',
        (oldOp _ _ _ hj).symm, hbl _ hb⟩
    · exact ⟨l.length, n, q, by simp, by simp [hpts, hlen], hn, rfl, hb⟩

theorem mem_of_assocLookup {α : Type} [DecidableEq α] {l : List (α × ℤ)} {a : α} {r : ℤ}
    (h : assocLookup l a = some r) : (a, r) ∈ l := by
  simp only [assocLookup, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some he
  have he1 := List.find?_some he
  simp only [decide_eq_true_eq] at he1
  rw [← he1]
  exact hm

theorem trNode_const_triv (consts : List ℤ) (powerW : ℕ) (s : TrState) {c : ℤ}
    (hc : ¬ IsNontrivial c) :
    trNode consts powerW s (.const c) = { s with nodePts := s.nodePts ++ [trivialRef c] } := by
  simp [trNode, hc]

theorem trNode_const_old (consts : List ℤ) (powerW : ℕ) (s : TrState) {c r : ℤ}
    (hc : IsNontrivial c) (hl : assocLookup s.constRefs c = some r) :
    trNode consts powerW s (.const c) = { s with nodePts := s.nodePts ++ [r] } := by
  simp [trNode, hc, hl]

theorem trNode_const_new (consts : List ℤ) (powerW : ℕ) (s : TrState) {c : ℤ}
    (hc : IsNontrivial c) (hl : assocLookup s.constRefs c = none) :
    trNode consts powerW s (.const c) = { s with
      next := s.next + 5 + 1
      nodePts := s.nodePts ++ [(s.next : ℤ)]
      constRefs := s.constRefs ++ [(c, (s.next : ℤ))]
      constants := s.constants ++ [(18 + consts.idxOf c, (s.next : ℤ), s.next + 5)] } := by
  simp only [trNode, hc, ite_true, hl]

theorem nodeInv_step {consts : List ℤ} {powerW p : ℕ} {sV : TrState} {alV : Alloc}
    {l : List NatNode} {s : TrState} {al : Alloc} (h : NodeInv consts powerW p sV alV l s al)
    (hwfl : ∀ (j : ℕ) (n' : NatNode), l[j]? = some n' → ∀ a ∈ n'.children, a < j)
    (n : NatNode) (hwf : ∀ a ∈ n.children, a < l.length) :
    NodeInv consts powerW p sV alV (l ++ [n]) (trNode consts powerW s n)
      (allocNode powerW s al n) := by
  have hlen := h.len
  have hge := h.next_ge
  by_cases hop : IsOpNode n
  · have hopf : opFor (s.nodePts ++ [(s.next : ℤ)]) s.next n = opFor s.nodePts s.next n :=
      opFor_append _ _ fun a ha => by rw [hlen]; exact hwf a ha
    rw [trNode_op consts powerW s hop, allocNode_op powerW s al hop]
    refine nodeInv_step_of h hwfl n _ _ (s.next : ℤ)
      (by show p + 3 ≤ s.next + 5 + opLen powerW n; omega)
      ((h.alloc.addSlot hge _).addBlock (by omega) (opLen powerW n)) rfl rfl rfl
      (fun e he => by simp [he]) (fun b hb => by simp [hb]) (fun d hd => hd)
      (fun op hop => by simp [hop]) ?_ (fun e he => Or.inl he) (fun d hd => Or.inl hd)
      (fun e he => he) ?_ ?_
    · have hsl : (s.next, Slot.node l.length) ∈
          al.slots ++ [(s.next, Slot.node s.nodePts.length)] := by simp [hlen]
      cases n <;> simp only [IsOpNode] at hop <;> simp only [NodePt] <;>
        exact ⟨s.next, rfl, hsl, by rw [hopf]; simp⟩
    · intro op hop'
      simp only [List.mem_append, List.mem_singleton] at hop'
      rcases hop' with hop' | rfl
      · exact Or.inl hop'
      · exact Or.inr ⟨s.next, rfl, hop, hopf.symm, by simp⟩
    · have := h.perm.append_right [(s.next + 5, opLen powerW n)]
      simpa [formulaBlocks, opBlk_opFor powerW _ _ hop] using this
  · cases n with
    | var i =>
      refine nodeInv_step_of h hwfl _ _ _ ((assocLookup s.varRefs i).getD (-4)) hge h.alloc
        rfl rfl rfl (fun e he => he) (fun b hb => hb) (fun d hd => hd) (fun op hop => hop)
        rfl (fun e he => Or.inl he) (fun d hd => Or.inl hd) (fun e he => he)
        (fun op hop => Or.inl hop) h.perm
    | const c =>
      by_cases hc : IsNontrivial c
      · cases hl : assocLookup s.constRefs c with
        | some r =>
          rw [trNode_const_old consts powerW s hc hl]
          have hal : allocNode powerW s al (.const c) = al := by
            simp [allocNode, hl]
          rw [hal]
          obtain ⟨-, q, hq, h1, h2, -⟩ := h.constRefs _ (mem_of_assocLookup hl)
          refine nodeInv_step_of h hwfl _ _ _ r hge h.alloc
            rfl rfl rfl (fun e he => he) (fun b hb => hb) (fun d hd => hd) (fun op hop => hop)
            ⟨fun _ => ⟨q, hq, h1, h2⟩, fun h' => absurd hc h'⟩ (fun e he => Or.inl he)
            (fun d hd => Or.inl hd) (fun e he => he) (fun op hop => Or.inl hop) h.perm
        | none =>
          rw [trNode_const_new consts powerW s hc hl]
          have hal : allocNode powerW s al (.const c) =
              ⟨al.slots ++ [(s.next, Slot.const c)], al.blocks ++ [(s.next + 5, 1)]⟩ := by
            simp [allocNode, hc, hl]
          rw [hal]
          refine nodeInv_step_of h hwfl _ _ _ (s.next : ℤ) (by show p + 3 ≤ s.next + 5 + 1; omega)
            ((h.alloc.addSlot hge _).addBlock (by omega) 1) rfl rfl rfl
            (fun e he => by simp [he]) (fun b hb => by simp [hb]) (fun d hd => by simp [hd])
            (fun op hop => hop) ⟨fun _ => ⟨s.next, rfl, by simp, by simp⟩, fun h' => absurd hc h'⟩
            ?_ ?_ (fun e he => by simp [he]) (fun op hop => Or.inl hop) ?_
          · intro e he
            simp only [List.mem_append, List.mem_singleton] at he
            rcases he with he | rfl
            · exact Or.inl he
            · exact Or.inr ⟨hc, s.next, rfl, by simp, by simp, rfl, rfl⟩
          · intro d hd
            simp only [List.mem_append, List.mem_singleton] at hd
            rcases hd with hd | rfl
            · exact Or.inl hd
            · exact Or.inr ⟨⟨(c, (s.next : ℤ)), by simp, s.next, rfl, rfl⟩, by simp⟩
          · refine List.Perm.trans ?_ (h.perm.append_right [(s.next + 5, 1)])
            simp only [formulaBlocks, List.map_append, List.map_cons, List.map_nil, constBlk,
              List.append_assoc]
            exact List.Perm.append_left _ (List.Perm.append_left _ List.perm_append_comm)
      · rw [trNode_const_triv consts powerW s hc]
        have hal : allocNode powerW s al (.const c) = al := by simp [allocNode, hc]
        rw [hal]
        refine nodeInv_step_of h hwfl _ _ _ (trivialRef c) hge h.alloc
          rfl rfl rfl (fun e he => he) (fun b hb => hb) (fun d hd => hd) (fun op hop => hop)
          ⟨fun h' => absurd h' hc, fun _ => rfl⟩ (fun e he => Or.inl he)
          (fun d hd => Or.inl hd) (fun e he => he) (fun op hop => Or.inl hop) h.perm
    | _ => exact absurd trivial hop

theorem nodeInv_foldl (consts : List ℤ) (powerW p : ℕ) {k : ℕ} {natIn : Bool}
    {lv : List (ℕ × VarKind)} {sV : TrState} {alV : Alloc} (hV : VarInv k natIn p lv sV alV)
    (l : List NatNode)
    (hwfl : ∀ (j : ℕ) (n' : NatNode), l[j]? = some n' → ∀ a ∈ n'.children, a < j) :
    NodeInv consts powerW p sV alV l
      (l.foldl (fun sa n => (trNode consts powerW sa.1 n, allocNode powerW sa.1 sa.2 n))
        (sV, alV)).1
      (l.foldl (fun sa n => (trNode consts powerW sa.1 n, allocNode powerW sa.1 sa.2 n))
        (sV, alV)).2 := by
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨hV.next_ge, hV.alloc, rfl, rfl, fun e he => he, fun b hb => hb,
      by simp [hV.nodePts], fun j n pj hj => by simp at hj, ?_, ?_, ?_, ?_⟩
    · intro e he; simp [hV.constRefs] at he
    · intro d hd; simp [hV.constants] at hd
    · intro op hop; simp [hV.operations] at hop
    · simp [formulaBlocks, hV.constants, hV.operations, hV.natBlocks]
  | append_singleton l n ih =>
    have hl : ∀ (j : ℕ) (n' : NatNode), l[j]? = some n' → ∀ a ∈ n'.children, a < j :=
      fun j n' hj => hwfl j n' (getElem?_append_old hj)
    rw [foldl_pair_append]
    refine nodeInv_step (ih hl) hl n fun a ha => hwfl l.length n (by simp) a ha

/-! ### The translation -/

theorem assocLookup_of_mem {α : Type} [DecidableEq α] {l : List (α × ℤ)}
    (hl : (l.map Prod.fst).Nodup) {a : α} {r : ℤ} (h : (a, r) ∈ l) : assocLookup l a = some r := by
  unfold assocLookup
  cases hf : l.find? (fun e => decide (e.1 = a)) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf _ h)
  | some e =>
    have hm := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    simp only [decide_eq_true_eq] at he
    have := List.inj_on_of_nodup_map hl hm h he
    simp [this]

/-- The variable stage with its record. -/
def varFold (k : ℕ) (natIn : Bool) (p : ℕ) (l : List (ℕ × VarKind)) : TrState × Alloc :=
  l.foldl (fun sa v => (trVar k natIn sa.1 v, allocVar k natIn sa.1 sa.2 v)) (trInit p, ⟨[], []⟩)

/-- The node stage with its record. -/
def nodeFold (consts : List ℤ) (powerW : ℕ) (sa : TrState × Alloc) (l : List NatNode) :
    TrState × Alloc :=
  l.foldl (fun sa n => (trNode consts powerW sa.1 n, allocNode powerW sa.1 sa.2 n)) sa

/-- The full run with its record. -/
def trRun (consts : List ℤ) (N : NatCircuit) (mode : OutputMode) (natIn : Bool)
    (power : Option (ℕ × ℕ)) : TrState × Alloc :=
  nodeFold consts ((power.map Prod.snd).getD 0)
    (varFold N.inputCount natIn (trParams N.inputCount mode) N.explicitVars) N.nodes

theorem trRun_fst (consts : List ℤ) (N : NatCircuit) (mode : OutputMode) (natIn : Bool)
    (power : Option (ℕ × ℕ)) : (trRun consts N mode natIn power).1 =
      trState consts N mode natIn power := by
  have h1 : (varFold N.inputCount natIn (trParams N.inputCount mode) N.explicitVars).1 =
      trVarsState N mode natIn := foldl_pair_fst _ _ _ _ _
  rw [trRun, nodeFold, ← Prod.mk.eta (p := varFold _ _ _ _), foldl_pair_fst, h1]
  rfl

section

variable (consts : List ℤ) (N : NatCircuit) (mode : OutputMode) (natIn : Bool)
  (power : Option (ℕ × ℕ))

theorem trRun_varInv : VarInv N.inputCount natIn (trParams N.inputCount mode) N.explicitVars
    (varFold N.inputCount natIn (trParams N.inputCount mode) N.explicitVars).1
    (varFold N.inputCount natIn (trParams N.inputCount mode) N.explicitVars).2 :=
  varInv_foldl _ _ _ _

theorem trRun_nodeInv (hwf : NodesWF N.nodes) :
    NodeInv consts ((power.map Prod.snd).getD 0) (trParams N.inputCount mode)
      (varFold N.inputCount natIn (trParams N.inputCount mode) N.explicitVars).1
      (varFold N.inputCount natIn (trParams N.inputCount mode) N.explicitVars).2 N.nodes
      (trRun consts N mode natIn power).1 (trRun consts N mode natIn power).2 := by
  have := nodeInv_foldl consts ((power.map Prod.snd).getD 0) (trParams N.inputCount mode)
    (trRun_varInv N mode natIn) N.nodes fun j n hj a ha => by
      obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 hj
      exact hwf j hj' a ha
  simpa [trRun, nodeFold] using this

end

section

variable (consts : List ℤ) (N : NatCircuit) (mode : OutputMode) (natIn : Bool)
  (power : Option (ℕ × ℕ))

/-- The point reference of the explicit variable `i` in the translation. -/
def trVref (i : ℕ) : ℤ := (assocLookup (trRun consts N mode natIn power).1.varRefs i).getD (-4)

/-- The point reference of node `j` in the translation. -/
def trPt (j : ℕ) : ℤ := (trRun consts N mode natIn power).1.nodePts.getD j (-4)

/-- The fresh points of the translation: the input and output parameter points and the
allocated points. -/
def trSlots : List (ℕ × Slot) :=
  (List.range N.inputCount).map (fun i => (5 * i, Slot.var i)) ++
    (if mode = .value then [(5 * N.inputCount, Slot.out)] else []) ++
    (trRun consts N mode natIn power).2.slots

theorem translate_sources : (translate consts N mode natIn power).sources =
    (trRun consts N mode natIn power).1.sources := by rw [trRun_fst]; rfl

theorem translate_constants : (translate consts N mode natIn power).constants =
    (trRun consts N mode natIn power).1.constants := by rw [trRun_fst]; rfl

theorem translate_operations : (translate consts N mode natIn power).operations =
    (trRun consts N mode natIn power).1.operations := by rw [trRun_fst]; rfl

theorem translate_rootEq : (translate consts N mode natIn power).rootEq =
    (trPt consts N mode natIn power N.root, match mode with
      | .value => ((5 * N.inputCount : ℕ) : ℤ)
      | .zero => -1) := by
  rw [trPt, trRun_fst]; rfl

variable {consts N mode natIn power} {P : NatCircuit} {V : ℕ}

theorem trVref_spec (hwf : WellFormed P N V) {v : ℕ × VarKind} (hv : v ∈ N.explicitVars) :
    (IsInputVar N.inputCount v → trVref consts N mode natIn power v.1 = 5 * v.1) ∧
    (¬ IsInputVar N.inputCount v → ∃ q : ℕ, trVref consts N mode natIn power v.1 = q ∧
      (q, Slot.var v.1) ∈ (trRun consts N mode natIn power).2.slots) ∧
    (natFlag N.inputCount natIn v = true → ∃ st,
      (trVref consts N mode natIn power v.1, some st) ∈ (trRun consts N mode natIn power).1.sources) := by
  have hV := trRun_varInv N mode natIn
  have hN := trRun_nodeInv consts N mode natIn power hwf.core.args_lt
  obtain ⟨r, hr, h1, h2, h3⟩ := hV.var v hv
  have hkeys : ((varFold N.inputCount natIn (trParams N.inputCount mode)
      N.explicitVars).1.varRefs.map Prod.fst).Nodup := by
    rw [hV.keys]; exact hwf.core.vars_nodup
  have hvr : trVref consts N mode natIn power v.1 = r := by
    rw [trVref, hN.varRefs, assocLookup_of_mem hkeys hr]; rfl
  rw [hvr]
  refine ⟨h1, fun hI => ?_, fun hn => ?_⟩
  · obtain ⟨q, hq, hs⟩ := h2 hI
    exact ⟨q, hq, hN.slots_sub _ hs⟩
  · obtain ⟨st, hst, -⟩ := h3 hn
    exact ⟨st, by rw [hN.sources]; exact hst⟩

theorem trVref_eq_of_mem (hwf : WellFormed P N V) {i : ℕ} {r : ℤ}
    (h : (i, r) ∈ (varFold N.inputCount natIn (trParams N.inputCount mode) N.explicitVars).1.varRefs) :
    trVref consts N mode natIn power i = r := by
  have hV := trRun_varInv N mode natIn
  have hN := trRun_nodeInv consts N mode natIn power hwf.core.args_lt
  have hkeys : ((varFold N.inputCount natIn (trParams N.inputCount mode)
      N.explicitVars).1.varRefs.map Prod.fst).Nodup := by
    rw [hV.keys]; exact hwf.core.vars_nodup
  rw [trVref, hN.varRefs, assocLookup_of_mem hkeys h]; rfl

theorem trPt_spec (hwf : WellFormed P N V) {j : ℕ} (hj : j < N.nodes.length) :
    NodePt consts (trRun consts N mode natIn power).1 (trRun consts N mode natIn power).2 j
      (trPt consts N mode natIn power j) N.nodes[j] := by
  have hN := trRun_nodeInv consts N mode natIn power hwf.core.args_lt
  refine hN.pt j _ _ (List.getElem?_eq_getElem hj) ?_
  have hj' : j < (trRun consts N mode natIn power).1.nodePts.length := by rw [hN.len]; exact hj
  rw [List.getElem?_eq_getElem hj', trPt, List.getD_eq_getElem _ _ hj']

end

theorem natFlag_of {k : ℕ} {natIn : Bool} {v : ℕ × VarKind}
    (h : natIn = true ∨ v.2 = VarKind.witness) : natFlag k natIn v = true := by
  rcases h with h | h
  · simp [natFlag, h]
  · simp [natFlag, IsInputVar, h]

theorem natIn_or_witness {N : NatCircuit} {m V : ℕ} (hwf : WellFormedCore N m V) {natIn : Bool}
    {v : ℕ × VarKind} (hv : v ∈ N.explicitVars) (h : natFlag N.inputCount natIn v = true) :
    natIn = true ∨ v.2 = VarKind.witness := by
  cases natIn
  · right
    simp only [natFlag, Bool.or_false, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, IsInputVar, not_and] at h
    cases hk : v.2
    · exact absurd (lt_of_input hwf hv hk) (h hk)
    · rfl
  · exact Or.inl rfl

theorem isInputVar_of_lt {N : NatCircuit} {i : ℕ} (hi : i < N.inputCount) : IsInputVar N.inputCount (i, VarKind.input) := ⟨rfl, hi⟩

theorem not_isInputVar_of_witness {k : ℕ} {v : ℕ × VarKind} (h : v.2 = VarKind.witness) :
    ¬ IsInputVar k v := fun h' => by rw [h'.1] at h; cases h

/-- **The translation has the shape used by the semantics.** For a well-formed circuit whose
nontrivial constants have their fixed-scalar templates at the indices `18 + h` given by the
constant table, and with a power recipe when it has call nodes. -/
def translateShape (consts : List ℤ) (P N : NatCircuit) (V : ℕ) (mode : OutputMode)
    (natIn : Bool) (power : Option (ℕ × ℕ)) (templates recipes : List ExPoly)
    (scalarOf : ℤ → ExPoly) (hwf : WellFormed P N V)
    (hconst : ∀ c, NatNode.const c ∈ N.nodes → Nontrivial c →
      getEx templates (18 + consts.idxOf c) = scalarOf c)
    (hpow : HasCall N → power.isSome) :
    TranslationShape templates recipes scalarOf (translate consts N mode natIn power) P N
      (decide (mode = .value)) natIn where
  vref := trVref consts N mode natIn power
  pt := trPt consts N mode natIn power
  params := by cases mode <;> simp [Syntax.translate, trParams]
  vref_input i hi := by
    have := (trVref_spec (consts := consts) (mode := mode) (natIn := natIn) (power := power) hwf
      (input_mem hwf.core hi)).1 (isInputVar_of_lt hi)
    exact this
  row v hv hn := by
    obtain ⟨st, hst⟩ := (trVref_spec (consts := consts) (mode := mode) (natIn := natIn)
      (power := power) hwf hv).2.2 (natFlag_of hn)
    exact ⟨st, by rw [translate_sources]; exact hst⟩
  row_inv row hrow st hst := by
    rw [translate_sources, (trRun_nodeInv consts N mode natIn power hwf.core.args_lt).sources]
      at hrow
    obtain ⟨v, hv, hr, hn⟩ := (trRun_varInv N mode natIn).row row hrow
    exact ⟨v, hv, (trVref_eq_of_mem hwf hr).symm, natIn_or_witness hwf.core hv (hn st hst).1⟩
  pt_var j hj i hn := by
    have := trPt_spec (consts := consts) (mode := mode) (natIn := natIn) (power := power) hwf hj
    rw [hn] at this
    simp only [NodePt] at this
    exact this
  pt_zero j hj hn := by
    have := trPt_spec (consts := consts) (mode := mode) (natIn := natIn) (power := power) hwf hj
    rw [hn] at this
    exact this.2 (by simp [IsNontrivial])
  pt_one j hj hn := by
    have := trPt_spec (consts := consts) (mode := mode) (natIn := natIn) (power := power) hwf hj
    rw [hn] at this
    exact this.2 (by simp [IsNontrivial])
  pt_neg_one j hj hn := by
    have := trPt_spec (consts := consts) (mode := mode) (natIn := natIn) (power := power) hwf hj
    rw [hn] at this
    exact this.2 (by simp [IsNontrivial])
  pt_const j hj c hn hc := by
    have := trPt_spec (consts := consts) (mode := mode) (natIn := natIn) (power := power) hwf hj
    rw [hn] at this
    obtain ⟨q, hq, -, hd⟩ := this.1 hc
    refine ⟨_, by rw [translate_constants]; exact hd, hq.symm, ?_⟩
    exact hconst c (hn ▸ List.getElem_mem hj) hc
  const_inv d hd := by
    rw [translate_constants] at hd
    have hN := trRun_nodeInv consts N mode natIn power hwf.core.args_lt
    obtain ⟨⟨e, he, q, hq, rfl⟩, -⟩ := hN.constants d hd
    obtain ⟨hn, -, -, -, -, j, hj, hp⟩ := hN.constRefs e he
    obtain ⟨hj', hjn⟩ := List.getElem?_eq_some_iff.1 hj
    refine ⟨j, hj', e.1, hjn, hn, ?_, hconst e.1 (hjn ▸ List.getElem_mem hj') hn⟩
    obtain ⟨hp', hpe⟩ := List.getElem?_eq_some_iff.1 hp
    simp only [trPt, List.getD_eq_getElem _ _ hp', hpe, hq]
  op_add j hj a b hn := by
    have := trPt_spec (consts := consts) (mode := mode) (natIn := natIn) (power := power) hwf hj
    rw [hn] at this
    obtain ⟨q, hq, -, hop⟩ := this
    exact ⟨q + 5, by rw [translate_operations, hq]; exact hop⟩
  op_mul j hj a b hn := by
    have := trPt_spec (consts := consts) (mode := mode) (natIn := natIn) (power := power) hwf hj
    rw [hn] at this
    obtain ⟨q, hq, -, hop⟩ := this
    exact ⟨q + 5, by rw [translate_operations, hq]; exact hop⟩
  op_call j hj a b c w hn := by
    have := trPt_spec (consts := consts) (mode := mode) (natIn := natIn) (power := power) hwf hj
    rw [hn] at this
    obtain ⟨q, hq, -, hop⟩ := this
    exact ⟨q + 5, by rw [translate_operations, hq]; exact hop⟩
  op_inv op hop := by
    rw [translate_operations] at hop
    have hN := trRun_nodeInv consts N mode natIn power hwf.core.args_lt
    obtain ⟨j, n, q, hj, hp, hn, rfl, -⟩ := hN.ops op hop
    obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 hj
    obtain ⟨hp', hpe⟩ := List.getElem?_eq_some_iff.1 hp
    have hpt : trPt consts N mode natIn power j = q := by
      simp only [trPt, List.getD_eq_getElem _ _ hp', hpe]
    refine ⟨j, hj', ?_⟩
    generalize N.nodes[j] = n at hn
    cases n with
    | add a b => exact Or.inl ⟨a, b, q + 5, rfl, by rw [hpt]; rfl⟩
    | mul a b => exact Or.inr (Or.inl ⟨a, b, q + 5, rfl, by rw [hpt]; rfl⟩)
    | call a b c w => exact Or.inr (Or.inr ⟨a, b, c, w, q + 5, rfl, by rw [hpt]; rfl⟩)
    | _ => exact absurd hn id
  root := by
    rw [translate_rootEq]
    cases mode <;> simp
  power h := by simpa [Syntax.translate] using hpow h
  gen_distinct := by simp [Syntax.translate]
  slots := trSlots consts N mode natIn power
  slots_sep := by
    have hN := trRun_nodeInv consts N mode natIn power hwf.core.args_lt
    have hal := hN.alloc
    have hp : ∀ e ∈ (trRun consts N mode natIn power).2.slots,
        trParams N.inputCount mode + 3 ≤ e.1 := fun e he => (hal.slot_range e he).1
    have hpk : 5 * N.inputCount ≤ trParams N.inputCount mode := by
      cases mode <;> simp [trParams]
    unfold trSlots
    refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · refine List.pairwise_map.2 (List.pairwise_lt_range.imp fun {i i'} h => ?_)
      right; left; simp only; omega
    · split_ifs <;> simp
    · intro e he e' he'
      split_ifs at he' with hm
      · simp only [List.mem_map, List.mem_range] at he
        obtain ⟨i, hi, rfl⟩ := he
        simp only [List.mem_singleton] at he'
        subst he'
        right; left; simp only; omega
      · simp at he'
    · exact hal.slots_sep.imp fun h => Or.inr h
    · intro e he e' he'
      right
      have := hp e' he'
      simp only [List.mem_append, List.mem_map, List.mem_range] at he
      rcases he with ⟨i, hi, rfl⟩ | he
      · left; simp only; omega
      · split_ifs at he with hm
        · simp only [List.mem_singleton] at he
          subst he
          subst hm
          left; simp only [trParams] at this ⊢; omega
        · simp at he
  slots_gen e he m := by
    have hN := trRun_nodeInv consts N mode natIn power hwf.core.args_lt
    have hgen : (translate consts N mode natIn power).generator m =
        trParams N.inputCount mode + m := by
      fin_cases m <;> simp [Syntax.translate]
    rw [hgen]
    unfold trSlots at he
    simp only [List.mem_append, List.mem_map, List.mem_range] at he
    rcases he with (⟨i, hi, rfl⟩ | he) | he
    · have : 5 * N.inputCount ≤ trParams N.inputCount mode := by
        cases mode <;> simp [trParams]
      simp only; omega
    · split_ifs at he with hm
      · simp only [List.mem_singleton] at he
        subst he hm
        simp only [trParams]; omega
      · simp at he
    · have := (hN.alloc.slot_range e he).1
      omega
  slot_input i hi := by simp [trSlots, hi]
  slot_out h := by simp at h; simp [trSlots, h]
  slot_var v hv hw := by
    obtain ⟨q, hq, hs⟩ := (trVref_spec (consts := consts) (mode := mode) (natIn := natIn)
      (power := power) hwf hv).2.1 (not_isInputVar_of_witness hw)
    exact ⟨q, hq, by simp [trSlots, hs]⟩
  slot_node j hj hv hc := by
    have := trPt_spec (consts := consts) (mode := mode) (natIn := natIn) (power := power) hwf hj
    generalize N.nodes[j] = n at this hv hc
    cases n with
    | var i => exact absurd rfl (hv i)
    | const c => exact absurd rfl (hc c)
    | add a b =>
      obtain ⟨q, hq, hs, -⟩ := this
      exact ⟨q, hq, by simp [trSlots, hs]⟩
    | mul a b =>
      obtain ⟨q, hq, hs, -⟩ := this
      exact ⟨q, hq, by simp [trSlots, hs]⟩
    | call a b c w =>
      obtain ⟨q, hq, hs, -⟩ := this
      exact ⟨q, hq, by simp [trSlots, hs]⟩
  slot_const j hj c hn hc := by
    have := trPt_spec (consts := consts) (mode := mode) (natIn := natIn) (power := power) hwf hj
    rw [hn] at this
    obtain ⟨q, hq, hs, -⟩ := this.1 hc
    exact ⟨q, hq, by simp [trSlots, hs]⟩

end ZInQ.Translation
