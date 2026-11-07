import ZInQKernel.Syntax.Templates
import ZInQKernel.Compiler.Circuits

/-!
# Translation of a natural circuit into a model-evaluation recipe

Blueprint: `syntax/recipes/model-evaluation-translation.md`.

`translate consts N mode natInputs power` is the model-evaluation recipe of the natural circuit
`N` (`ZInQ.Compiler.Natural.NatCircuit`), a transcription of `Translator.translate` of
`construction/rational-circuit-translator.js`. One allocation counter starts at the parameter
count `p = 5(k + [value])`:

1. the generator indices `g₀, g₁, g₂` take the next three variables;
2. every explicit variable, in list order: an input `i` gets the point reference `5i`, any other
   variable a fresh point; then, unless it is an input and the inputs are unconstrained, a
   natural block of `140604` variables;
3. every node, in order, gets a point reference: `var i` the reference of `i`; `const 0, 1, -1`
   the references `-1, -2, -3`; any other constant `c`, at its first occurrence, a fresh point
   and a block of `1` with the constant definition `(18 + h, point, start)`, where `h` is the
   position of `c` in the constant table `consts` (template `18 + h` of the library is
   `S_{integer_constant_h}`), and later occurrences reuse that point; `add` and `mul` a fresh point
   and a block of `6` or `35134` with an operation of kind `0` or `1`; `call (a, b, c) w` a fresh
   point and a block of the witness count of the power recipe, with an operation of kind `2`;
4. the root equality is `(pt(root), 5k)` in value mode and `(pt(root), -1)` in zero mode;
5. the variable count is the final counter.

The operation templates are those of the library: `natural` (index `12`, `140604` witnesses),
`raw_add` (index `1`, `6` witnesses), `multiply` (index `11`, `35134` witnesses); the power recipe
is given as a pair (recipe index, witness count).

Ill-formed input is read totally: an input-kind variable of index at least `k` is treated as a
witness variable, a variable node without explicit variable and a node reference to a later
node get the reference `-4` (five zeros), and a constant missing from the table gets template
index `18 + consts.length`. None of this happens for the well-formed circuits translated here.

`translate_variableCount` gives the variable count in closed form.
-/

namespace ZInQ.Syntax

open ZInQ.Compiler.Natural (NatCircuit NatNode VarKind)

/-- The output mode of a translation. -/
inductive OutputMode
  /-- The root value is equated with an output code (parameters `5k, …, 5k+4`). -/
  | value
  /-- The root value is equated with the code of `O`. -/
  | zero
  deriving DecidableEq

/-- The state of a translation: the counter, the references of the explicit variables, the
source rows, the points of the nodes so far, the points of the constants so far, the constant
definitions and the operations. -/
structure TrState where
  /-- The allocation counter. -/
  next : ℕ
  /-- Explicit variable index and point reference. -/
  varRefs : List (ℕ × ℤ)
  /-- The source rows `(r, s)`. -/
  sources : List (ℤ × Option ℕ)
  /-- The point reference of every node translated so far. -/
  nodePts : List ℤ
  /-- Constant value and point reference, for the constants met so far. -/
  constRefs : List (ℤ × ℤ)
  /-- The constant definitions `(σ, r, s)`. -/
  constants : List (ℕ × ℤ × ℕ)
  /-- The operations. -/
  operations : List Operation

/-- Association-list lookup. -/
def assocLookup {α : Type} [DecidableEq α] (l : List (α × ℤ)) (a : α) : Option ℤ :=
  (l.find? fun e => decide (e.1 = a)).map Prod.snd

/-- The variable is an input of a circuit with `k` inputs. -/
def IsInputVar (k : ℕ) (v : ℕ × VarKind) : Prop := v.2 = .input ∧ v.1 < k

instance (k : ℕ) (v : ℕ × VarKind) : Decidable (IsInputVar k v) := by
  unfold IsInputVar; infer_instance

/-- Step 2: the row of one explicit variable. -/
def trVar (k : ℕ) (natInputs : Bool) (s : TrState) (v : ℕ × VarKind) : TrState :=
  let pt : ℤ := if IsInputVar k v then 5 * v.1 else s.next
  let n₁ : ℕ := if IsInputVar k v then s.next else s.next + 5
  let nat : Bool := !(decide (IsInputVar k v)) || natInputs
  { s with
    next := if nat then n₁ + 140604 else n₁
    varRefs := s.varRefs ++ [(v.1, pt)]
    sources := s.sources ++ [(pt, if nat then some n₁ else none)] }

/-- The constant is not `0`, `1` or `-1`. -/
def IsNontrivial (c : ℤ) : Prop := c ≠ 0 ∧ c ≠ 1 ∧ c ≠ -1

instance (c : ℤ) : Decidable (IsNontrivial c) := by unfold IsNontrivial; infer_instance

/-- The point reference of a trivial constant: `0 ↦ -1`, `1 ↦ -2`, `-1 ↦ -3`. -/
def trivialRef (c : ℤ) : ℤ := if c = 0 then -1 else if c = 1 then -2 else -3

/-- Step 3: the point of one node. -/
def trNode (consts : List ℤ) (powerW : ℕ) (s : TrState) : NatNode → TrState
  | .var i => { s with nodePts := s.nodePts ++ [(assocLookup s.varRefs i).getD (-4)] }
  | .const c =>
    if IsNontrivial c then
      match assocLookup s.constRefs c with
      | some r => { s with nodePts := s.nodePts ++ [r] }
      | none =>
        { s with
          next := s.next + 5 + 1
          nodePts := s.nodePts ++ [(s.next : ℤ)]
          constRefs := s.constRefs ++ [(c, (s.next : ℤ))]
          constants := s.constants ++ [(18 + consts.idxOf c, (s.next : ℤ), s.next + 5)] }
    else { s with nodePts := s.nodePts ++ [trivialRef c] }
  | .add a b =>
    { s with
      next := s.next + 5 + 6
      nodePts := s.nodePts ++ [(s.next : ℤ)]
      operations := s.operations ++
        [.add (s.nodePts.getD a (-4)) (s.nodePts.getD b (-4)) s.next (s.next + 5)] }
  | .mul a b =>
    { s with
      next := s.next + 5 + 35134
      nodePts := s.nodePts ++ [(s.next : ℤ)]
      operations := s.operations ++
        [.mul (s.nodePts.getD a (-4)) (s.nodePts.getD b (-4)) s.next (s.next + 5)] }
  | .call a b c _ =>
    { s with
      next := s.next + 5 + powerW
      nodePts := s.nodePts ++ [(s.next : ℤ)]
      operations := s.operations ++
        [.power (s.nodePts.getD a (-4)) (s.nodePts.getD b (-4)) (s.nodePts.getD c (-4)) s.next
          (s.next + 5)] }

/-- The parameter count `5(k + [value])`. -/
def trParams (k : ℕ) (mode : OutputMode) : ℕ :=
  match mode with
  | .value => 5 * (k + 1)
  | .zero => 5 * k

/-- The state after steps 1 and 2. -/
def trVarsState (N : NatCircuit) (mode : OutputMode) (natInputs : Bool) : TrState :=
  N.explicitVars.foldl (trVar N.inputCount natInputs)
    ⟨trParams N.inputCount mode + 3, [], [], [], [], [], []⟩

/-- The state after step 3. -/
def trState (consts : List ℤ) (N : NatCircuit) (mode : OutputMode) (natInputs : Bool)
    (power : Option (ℕ × ℕ)) : TrState :=
  N.nodes.foldl (trNode consts ((power.map Prod.snd).getD 0)) (trVarsState N mode natInputs)

/-- **Translation of a natural circuit into a model-evaluation recipe**, with constant table
`consts`, output mode `mode`, natural constraints on the inputs iff `natInputs`, and optional
power recipe `power = (recipe index, witness count)`. -/
def translate (consts : List ℤ) (N : NatCircuit) (mode : OutputMode) (natInputs : Bool)
    (power : Option (ℕ × ℕ)) : ModelRecipe :=
  let p := trParams N.inputCount mode
  let s := trState consts N mode natInputs power
  { parameterCount := p
    variableCount := s.next
    generator := ![p, p + 1, p + 2]
    sources := s.sources
    constants := s.constants
    operations := s.operations
    rootEq := (s.nodePts.getD N.root (-4),
      match mode with
      | .value => ((5 * N.inputCount : ℕ) : ℤ)
      | .zero => -1)
    natural := 12
    addition := 1
    multiplication := 11
    power := power.map Prod.fst }

/-! ### The variable count -/

/-- The variables taken by one explicit variable: a fresh point unless it is an input, and a
natural block unless it is an unconstrained input. -/
def varCost (k : ℕ) (natInputs : Bool) (v : ℕ × VarKind) : ℕ :=
  if IsInputVar k v then (if natInputs then 140604 else 0) else 5 + 140604

/-- The variables taken by an addition, multiplication or call node. -/
def nodeCost (powerW : ℕ) : NatNode → ℕ
  | .add _ _ => 5 + 6
  | .mul _ _ => 5 + 35134
  | .call _ _ _ _ => 5 + powerW
  | _ => 0

/-- The value of a nontrivial constant node. -/
def nontrivialConst : NatNode → Option ℤ
  | .const c => if IsNontrivial c then some c else none
  | _ => none

theorem trVar_next (k : ℕ) (natInputs : Bool) (s : TrState) (v : ℕ × VarKind) :
    (trVar k natInputs s v).next = s.next + varCost k natInputs v := by
  unfold trVar varCost
  by_cases h : IsInputVar k v
  · cases natInputs <;> simp [h]
  · cases natInputs <;> simp [h, Nat.add_assoc]

theorem foldl_trVar_next (k : ℕ) (natInputs : Bool) (l : List (ℕ × VarKind)) (s : TrState) :
    (l.foldl (trVar k natInputs) s).next = s.next + (l.map (varCost k natInputs)).sum := by
  induction l generalizing s with
  | nil => simp
  | cons v l ih => rw [List.foldl_cons, ih, trVar_next, List.map_cons, List.sum_cons, Nat.add_assoc]

@[simp] theorem trVar_constRefs (k : ℕ) (natInputs : Bool) (s : TrState) (v : ℕ × VarKind) :
    (trVar k natInputs s v).constRefs = s.constRefs := rfl

theorem foldl_trVar_constRefs (k : ℕ) (natInputs : Bool) (l : List (ℕ × VarKind))
    (s : TrState) : (l.foldl (trVar k natInputs) s).constRefs = s.constRefs := by
  induction l generalizing s with
  | nil => rfl
  | cons v l ih => simp [ih]

theorem assocLookup_eq_none {α : Type} [DecidableEq α] {l : List (α × ℤ)} {a : α} :
    assocLookup l a = none ↔ a ∉ l.map Prod.fst := by
  simp only [assocLookup, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq,
    List.mem_map, not_exists, not_and]

theorem assocLookup_eq_some {α : Type} [DecidableEq α] {l : List (α × ℤ)} {a : α} {r : ℤ}
    (h : assocLookup l a = some r) : a ∈ l.map Prod.fst := by
  by_contra hn
  rw [← assocLookup_eq_none] at hn
  rw [hn] at h
  cases h

/-- One node step: the counter grows by the node cost, plus `6` for a new constant, which is
then recorded. -/
theorem trNode_step (consts : List ℤ) (powerW : ℕ) (s : TrState) (n : NatNode)
    (hs : (s.constRefs.map Prod.fst).Nodup) :
    (trNode consts powerW s n).next + 6 * (s.constRefs.map Prod.fst).length =
        s.next + nodeCost powerW n + 6 * ((trNode consts powerW s n).constRefs.map Prod.fst).length ∧
      ((trNode consts powerW s n).constRefs.map Prod.fst).Nodup ∧
      ∀ c, c ∈ (trNode consts powerW s n).constRefs.map Prod.fst ↔
        c ∈ s.constRefs.map Prod.fst ∨ nontrivialConst n = some c := by
  cases n with
  | const c =>
    simp only [trNode, nodeCost, nontrivialConst]
    by_cases hc : IsNontrivial c
    · simp only [hc, ite_true]
      cases hl : assocLookup s.constRefs c with
      | some r =>
        have hm := assocLookup_eq_some hl
        refine ⟨by simp, hs, fun d => ?_⟩
        simp only [Option.some.injEq]
        constructor
        · exact Or.inl
        · rintro (h | rfl)
          · exact h
          · exact hm
      | none =>
        have hm := assocLookup_eq_none.1 hl
        refine ⟨by simp; omega, ?_, fun d => ?_⟩
        · simp only [List.map_append, List.map_cons, List.map_nil]
          refine List.nodup_append.2 ⟨hs, List.nodup_singleton _, fun a ha b hb => ?_⟩
          rw [List.mem_singleton] at hb
          subst hb
          exact fun h => hm (h ▸ ha)
        · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
            List.mem_singleton, Option.some.injEq]
          constructor
          · rintro (h | rfl)
            · exact Or.inl h
            · exact Or.inr rfl
          · rintro (h | rfl)
            · exact Or.inl h
            · exact Or.inr rfl
    · simp [hc, hs]
  | var i => simp [trNode, nodeCost, nontrivialConst, hs]
  | add a b => simp [trNode, nodeCost, nontrivialConst, hs, Nat.add_assoc]
  | mul a b => simp [trNode, nodeCost, nontrivialConst, hs, Nat.add_assoc]
  | call a b c w => simp [trNode, nodeCost, nontrivialConst, hs, Nat.add_assoc]

theorem foldl_trNode (consts : List ℤ) (powerW : ℕ) (l : List NatNode) (s : TrState)
    (hs : (s.constRefs.map Prod.fst).Nodup) :
    (l.foldl (trNode consts powerW) s).next + 6 * (s.constRefs.map Prod.fst).length =
        s.next + (l.map (nodeCost powerW)).sum +
          6 * ((l.foldl (trNode consts powerW) s).constRefs.map Prod.fst).length ∧
      ((l.foldl (trNode consts powerW) s).constRefs.map Prod.fst).Nodup ∧
      ∀ c, c ∈ (l.foldl (trNode consts powerW) s).constRefs.map Prod.fst ↔
        c ∈ s.constRefs.map Prod.fst ∨ c ∈ l.filterMap nontrivialConst := by
  induction l generalizing s with
  | nil => simp [hs]
  | cons n l ih =>
    obtain ⟨h1, h2, h3⟩ := trNode_step consts powerW s n hs
    obtain ⟨k1, k2, k3⟩ := ih (trNode consts powerW s n) h2
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    refine ⟨by omega, k2, fun c => ?_⟩
    rw [k3, h3, List.filterMap_cons]
    cases hn : nontrivialConst n <;> simp [or_assoc, eq_comm]

/-- **The variable count of a translation**: the parameters, the three generator variables, the
cost of every explicit variable, the cost of every addition, multiplication and call node, and
`5 + 1` for every distinct nontrivial constant. -/
theorem translate_variableCount (consts : List ℤ) (N : NatCircuit) (mode : OutputMode)
    (natInputs : Bool) (power : Option (ℕ × ℕ)) :
    (translate consts N mode natInputs power).variableCount =
      trParams N.inputCount mode + 3 +
        (N.explicitVars.map (varCost N.inputCount natInputs)).sum +
        (N.nodes.map (nodeCost ((power.map Prod.snd).getD 0))).sum +
        6 * (N.nodes.filterMap nontrivialConst).toFinset.card := by
  have hc : (trVarsState N mode natInputs).constRefs = [] :=
    foldl_trVar_constRefs _ _ _ _
  have hv : (trVarsState N mode natInputs).next = trParams N.inputCount mode + 3 +
      (N.explicitVars.map (varCost N.inputCount natInputs)).sum := by
    rw [trVarsState, foldl_trVar_next]
  have h0 : ((trVarsState N mode natInputs).constRefs.map Prod.fst).Nodup := by
    rw [hc]; exact List.nodup_nil
  obtain ⟨h1, h2, h3⟩ := foldl_trNode consts ((power.map Prod.snd).getD 0) N.nodes _ h0
  rw [hc] at h1 h3
  have hlen : ((N.nodes.foldl (trNode consts ((power.map Prod.snd).getD 0))
      (trVarsState N mode natInputs)).constRefs.map Prod.fst).length =
      (N.nodes.filterMap nontrivialConst).toFinset.card := by
    rw [← List.toFinset_card_of_nodup h2]
    congr 1
    ext c
    simp [h3]
  show (N.nodes.foldl (trNode consts ((power.map Prod.snd).getD 0))
    (trVarsState N mode natInputs)).next = _
  rw [hlen, hv] at h1
  simp only [List.map_nil, List.length_nil, Nat.mul_zero, Nat.add_zero] at h1
  rw [h1]

end ZInQ.Syntax
