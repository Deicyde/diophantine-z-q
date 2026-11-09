import ZInQKernel.Compiler.Translation.Values
import ZInQKernel.Compiler.Circuits.Builder
import ZInQKernel.Syntax.Language.Lifting

/-!
# Well-formed natural circuits

A natural circuit `𝒩` with `k` inputs, explicit variables `(i₀, κ₀), (i₁, κ₁), …`, nodes
`n₀, …, n_{K-1}`, root `ρ` and power template `𝒫` with `V_𝒫` variables is *well-formed with
bound `V`* when

1. the explicit variable indices are pairwise distinct, the first `k` entries are the inputs
   with indices `0, …, k-1`, and no later entry is an input;
2. every argument of an `add`, `mul` or `call` node `n_j` is below `j`, and `ρ < K`;
3. every `var i` node refers to an explicit variable `i`;
4. every `const c` node with `c ∉ {0, 1, -1}` has `c ≥ 2`;
5. the blocks `[w, w + V_𝒫 - 3)` of distinct call nodes are pairwise disjoint and disjoint from
   the explicit variable indices;
6. every explicit variable index and every block variable is below `V`;
7. if `𝒩` has a call node, `𝒫` has `3` inputs, no call nodes, and is itself well-formed with
   bound `V_𝒫`, its explicit variables being `0, …, V_𝒫 - 1`.

Conditions 1–6 for a block length `m` form `WellFormedCore N m V`; the power template is checked
with block length `0` (it has no blocks). Under conditions 2, 3, 5 and 7, `val_θ(j)` depends
only on `θ` at the explicit variables and at the blocks of the call nodes up to `j`
(`nodeVal_congr`, `nodeVal_update_block`).

(Blueprint: `compiler/translation/natural-circuit-well-formed.md`.)
-/

namespace ZInQ.Translation

open Compiler.Natural Syntax

/-- Conditions 1–6 of well-formedness, for call blocks of length `m` and bound `V`. -/
structure WellFormedCore (N : NatCircuit) (m V : ℕ) : Prop where
  /-- The explicit variable indices are pairwise distinct. -/
  vars_nodup : (N.explicitVars.map Prod.fst).Nodup
  /-- The first `k` explicit variables are the inputs `0, …, k-1`. -/
  inputs_first : N.explicitVars.take N.inputCount =
    (List.range N.inputCount).map fun i => (i, VarKind.input)
  /-- There are at least `k` explicit variables. -/
  inputs_le : N.inputCount ≤ N.explicitVars.length
  /-- No later explicit variable is an input. -/
  later_witness : ∀ v ∈ N.explicitVars.drop N.inputCount, v.2 = VarKind.witness
  /-- Every argument of a node is an earlier node. -/
  args_lt : NodesWF N.nodes
  /-- The root is a node. -/
  root_lt : N.root < N.nodes.length
  /-- Every variable node refers to an explicit variable. -/
  var_explicit : ∀ i, NatNode.var i ∈ N.nodes → ∃ v ∈ N.explicitVars, v.1 = i
  /-- Every nontrivial constant is at least `2`. -/
  const_ge_two : ∀ c, NatNode.const c ∈ N.nodes → c ≠ 0 → c ≠ 1 → c ≠ -1 → 2 ≤ c
  /-- The blocks of distinct call nodes are pairwise disjoint. -/
  blocks_disjoint : N.blocks.Pairwise fun w w' => BlockDisjoint (w, m) (w', m)
  /-- The blocks avoid the explicit variables. -/
  blocks_explicit : ∀ w ∈ N.blocks, ∀ v ∈ N.explicitVars, ¬ InBlock (w, m) v.1
  /-- The explicit variables are below `V`. -/
  vars_lt : ∀ v ∈ N.explicitVars, v.1 < V
  /-- The block variables are below `V`. -/
  blocks_lt : ∀ w ∈ N.blocks, ∀ i, InBlock (w, m) i → i < V

/-- `𝒩` has a call node. -/
def HasCall (N : NatCircuit) : Prop := ∃ a b c w, NatNode.call a b c w ∈ N.nodes

/-- **Well-formed natural circuits** with power template `𝒫` and bound `V`. -/
structure WellFormed (P N : NatCircuit) (V : ℕ) : Prop where
  /-- Conditions 1–6, with call blocks of length `V_𝒫 - 3`. -/
  core : WellFormedCore N (P.varCount - 3) V
  /-- Condition 7. -/
  power : HasCall N → P.inputCount = 3 ∧ (∀ a b c w, NatNode.call a b c w ∉ P.nodes) ∧
    WellFormedCore P 0 P.varCount ∧ P.explicitVars.map Prod.fst = List.range P.varCount

/-! ### Locality of values -/

theorem mem_blocks_iff {N : NatCircuit} {w : ℕ} :
    w ∈ N.blocks ↔ ∃ a b c, NatNode.call a b c w ∈ N.nodes := by
  simp only [NatCircuit.blocks, List.mem_filterMap]
  constructor
  · rintro ⟨n, hn, h⟩
    cases n <;> simp at h
    subst h
    exact ⟨_, _, _, hn⟩
  · rintro ⟨a, b, c, h⟩
    exact ⟨_, h, rfl⟩

/-- Node values depend only on `θ` at the variables of the variable nodes and on the call values
at the blocks of the call nodes. -/
theorem nodeValues_congr {cv cv' : ℤ → ℤ → ℤ → ℕ → ℤ} {θ θ' : ℕ → ℤ} {l : List NatNode}
    (hvar : ∀ i, NatNode.var i ∈ l → θ i = θ' i)
    (hcall : ∀ a b c w, NatNode.call a b c w ∈ l → ∀ x y z, cv x y z w = cv' x y z w) :
    nodeValues cv θ l = nodeValues cv' θ' l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l n ih =>
    rw [nodeValues_append, nodeValues_append,
      ih (fun i hi => hvar i (by simp [hi])) (fun a b c w h => hcall a b c w (by simp [h]))]
    congr 1
    cases n with
    | var i => simp [nodeValue, hvar i (by simp)]
    | call a b c w => simp [nodeValue, hcall a b c w (by simp)]
    | _ => rfl

/-- The values of a prefix of the node list are a prefix of the values. -/
theorem nodeValues_append_left (cv : ℤ → ℤ → ℤ → ℕ → ℤ) (θ : ℕ → ℤ) (l l' : List NatNode) :
    nodeValues cv θ l <+: nodeValues cv θ (l ++ l') := by
  induction l' using List.reverseRecOn with
  | nil => simp
  | append_singleton l' n ih =>
    rw [← List.append_assoc, nodeValues_append]
    exact ih.trans (List.prefix_append _ _)

theorem getD_nodeValues_take (cv : ℤ → ℤ → ℤ → ℕ → ℤ) (θ : ℕ → ℤ) (l : List NatNode)
    {j t : ℕ} (hj : j < t) :
    (nodeValues cv θ l).getD j 0 = (nodeValues cv θ (l.take t)).getD j 0 := by
  rcases Nat.lt_or_ge j l.length with hl | hl
  · have hp := nodeValues_append_left cv θ (l.take t) (l.drop t)
    rw [List.take_append_drop] at hp
    have hlen : j < (nodeValues cv θ (l.take t)).length := by
      rw [length_nodeValues, List.length_take]; omega
    rw [List.getD_eq_getElem _ _ (hp.length_le.trans_lt' hlen), List.getD_eq_getElem _ _ hlen]
    exact (hp.getElem hlen).symm
  · rw [List.getD_eq_default _ _ (by rw [length_nodeValues]; exact hl),
      List.getD_eq_default _ _ (by rw [length_nodeValues, List.length_take]; omega)]

/-- The value of node `j` is the value computed from the first `t > j` nodes. -/
theorem nodeVal_eq_take (P N : NatCircuit) (θ : ℕ → ℤ) {j t : ℕ} (hj : j < t) :
    nodeVal P N θ j = (nodeValues (callValue P θ) θ (N.nodes.take t)).getD j 0 :=
  getD_nodeValues_take _ θ N.nodes hj

/-- One step of the value recursion: node `j` from the values of the earlier nodes. -/
theorem nodeVal_eq_nodeValue (P N : NatCircuit) (θ : ℕ → ℤ) {j : ℕ} (hj : j < N.nodes.length) :
    nodeVal P N θ j = nodeValue (callValue P θ) θ (nodeValues (callValue P θ) θ (N.nodes.take j))
      N.nodes[j] := by
  rw [nodeVal, nodeVals, nodeValues]
  exact getD_foldl_snoc _ N.nodes hj 0

/-- In a well-formed node list, the arguments of node `j` are read from all node values. -/
theorem nodeVal_eq_nodeValue_of_wf (P N : NatCircuit) (θ : ℕ → ℤ) (hwf : NodesWF N.nodes)
    {j : ℕ} (hj : j < N.nodes.length) :
    nodeVal P N θ j = nodeValue (callValue P θ) θ (nodeVals P N θ) N.nodes[j] := by
  rw [nodeVal_eq_nodeValue P N θ hj]
  have hc := hwf j hj
  have key : ∀ i, i < j → (nodeValues (callValue P θ) θ (N.nodes.take j)).getD i 0 =
      (nodeVals P N θ).getD i 0 := fun i hi => (getD_nodeValues_take _ θ N.nodes hi).symm
  generalize N.nodes[j] = n at hc
  cases n with
  | const c => rfl
  | var i => rfl
  | add a b =>
    simp only [NatNode.children, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hc
    simp only [nodeValue, key a hc.1, key b hc.2]
  | mul a b =>
    simp only [NatNode.children, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hc
    simp only [nodeValue, key a hc.1, key b hc.2]
  | call a b c w =>
    simp only [NatNode.children, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hc
    simp only [nodeValue, key a hc.1, key b hc.2.1, key c hc.2.2]

/-- `T_𝒫(y)` depends only on `y` at the variable nodes of `𝒫`. -/
theorem templateValue_congr {P : NatCircuit} {y y' : ℕ → ℤ}
    (h : ∀ i, NatNode.var i ∈ P.nodes → y i = y' i) : templateValue P y = templateValue P y' := by
  rw [templateValue, templateValue, nodeValues_congr h fun _ _ _ _ _ _ _ _ => rfl]

/-- For a well-formed power template, `T_𝒫(y)` depends only on `y` below `V_𝒫`. -/
theorem templateValue_congr_of_core {P : NatCircuit} (hP : WellFormedCore P 0 P.varCount)
    {y y' : ℕ → ℤ} (h : ∀ i < P.varCount, y i = y' i) : templateValue P y = templateValue P y' :=
  templateValue_congr fun i hi => by
    obtain ⟨v, hv, rfl⟩ := hP.var_explicit i hi
    exact h _ (hP.vars_lt v hv)

/-- A call value depends only on `θ` on the call's block `[w, w + V_𝒫 - 3)`. -/
theorem callValue_congr {P : NatCircuit} (hP : WellFormedCore P 0 P.varCount) {θ θ' : ℕ → ℤ}
    {w : ℕ} (h : ∀ i, InBlock (w, P.varCount - 3) i → θ i = θ' i) (a b c : ℤ) :
    callValue P θ a b c w = callValue P θ' a b c w := by
  refine templateValue_congr_of_core hP fun i hi => ?_
  simp only [callAssign]
  split_ifs with h3
  · rfl
  · exact h _ ⟨by simp, by simp only; omega⟩

/-- **Locality of values.** If `θ` and `θ'` agree at the explicit variables and on the blocks of
the call nodes, the node values agree. -/
theorem nodeVals_congr {P N : NatCircuit} {V : ℕ} (hwf : WellFormed P N V) {θ θ' : ℕ → ℤ}
    (hvar : ∀ v ∈ N.explicitVars, θ v.1 = θ' v.1)
    (hblock : ∀ w ∈ N.blocks, ∀ i, InBlock (w, P.varCount - 3) i → θ i = θ' i) :
    nodeVals P N θ = nodeVals P N θ' := by
  refine nodeValues_congr (fun i hi => ?_) fun a b c w hc x y z => ?_
  · obtain ⟨v, hv, rfl⟩ := hwf.core.var_explicit i hi
    exact hvar v hv
  · exact callValue_congr (hwf.power ⟨a, b, c, w, hc⟩).2.2.1
      (hblock w (mem_blocks_iff.2 ⟨a, b, c, hc⟩)) x y z

/-- The value of the circuit depends only on `θ` at the explicit variables and the blocks. -/
theorem circuitValue_congr {P N : NatCircuit} {V : ℕ} (hwf : WellFormed P N V) {θ θ' : ℕ → ℤ}
    (hvar : ∀ v ∈ N.explicitVars, θ v.1 = θ' v.1)
    (hblock : ∀ w ∈ N.blocks, ∀ i, InBlock (w, P.varCount - 3) i → θ i = θ' i) :
    circuitValue P N θ = circuitValue P N θ' := by
  rw [circuitValue, circuitValue, nodeVal, nodeVal, nodeVals_congr hwf hvar hblock]

/-- In particular the value depends only on `θ` below the bound `V`. -/
theorem circuitValue_congr_lt {P N : NatCircuit} {V : ℕ} (hwf : WellFormed P N V)
    {θ θ' : ℕ → ℤ} (h : ∀ i < V, θ i = θ' i) : circuitValue P N θ = circuitValue P N θ' :=
  circuitValue_congr hwf (fun v hv => h _ (hwf.core.vars_lt v hv))
    fun w hw i hi => h _ (hwf.core.blocks_lt w hw i hi)

end ZInQ.Translation
