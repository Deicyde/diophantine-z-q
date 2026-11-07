import ZInQKernel.Compiler.Universal.Specialize

/-!
# Counts and well-scopedness of the specialization

For a two-input circuit `ℋ` whose explicit variables begin with `X_0, X_1` and whose node list
begins with their variable nodes (and has no other node `var 0`):

1. `specialize ℋ c₃` has `9 + (e - 2)` explicit variables (`e` those of `ℋ`), the blocks of `ℋ`
   shifted by `7`, variable count `V + 7`, and `52` more nodes than `ℋ`: one variable node fewer
   and one constant node more in the renamed copy, plus `8` variable, `3` constant, `20` addition
   and `21` multiplication nodes; its constants are `c₃`, those of `ℋ`, then `1, 2, -1`.
2. If `ℋ` is well scoped, so is `specialize ℋ c₃`.

(Blueprint: `compiler/natural/universal/precision-circuit-specialization.md`, well-scopedness;
`circuit-node-counts.md`, for an arbitrary two-input circuit.)
-/

noncomputable section

namespace ZInQ.Compiler.Universal

open Natural Syntax

variable (H : NatCircuit) (code : ℤ)

/-! ### Counts -/

theorem specialize_inputCount : (specialize H code).inputCount = 5 := rfl

theorem specialize_varCount : (specialize H code).varCount = H.varCount + 7 := rfl

theorem specialize_explicitVars_length :
    (specialize H code).explicitVars.length = 9 + (H.explicitVars.length - 2) := by
  simp [specialize]

theorem specialize_nodes_length :
    (specialize H code).nodes.length = H.nodes.length + 52 := by
  simp [specialize, appendedNodes, pairingBlock]

theorem callW_renameNode (n : NatNode) :
    NatNode.callW (renameNode code n) = (NatNode.callW n).map (· + 7) := by
  cases n with
  | var i => rcases i with _ | _ | i <;> rfl
  | _ => rfl

theorem blocks_eq_filterMap (C : NatCircuit) : C.blocks = C.nodes.filterMap NatNode.callW := by
  unfold NatCircuit.blocks
  congr 1

theorem specialize_blocks : (specialize H code).blocks = H.blocks.map (· + 7) := by
  rw [blocks_eq_filterMap, blocks_eq_filterMap]
  simp only [specialize, List.filterMap_append, List.filterMap_map]
  have happ : (appendedNodes H.nodes.length H.root).filterMap NatNode.callW = [] := by
    simp [appendedNodes, pairingBlock, NatNode.callW]
  rw [happ, List.append_nil, List.map_filterMap]
  congr 1
  funext n
  exact callW_renameNode code n

theorem specialize_blocks_length : (specialize H code).blocks.length = H.blocks.length := by
  rw [specialize_blocks, List.length_map]

theorem appendedNodes_countKind (L ρ : ℕ) :
    countKind .var (appendedNodes L ρ) = 8 ∧ countKind .const (appendedNodes L ρ) = 3 ∧
    countKind .add (appendedNodes L ρ) = 20 ∧ countKind .mul (appendedNodes L ρ) = 21 ∧
    countKind .call (appendedNodes L ρ) = 0 ∧
    constList (appendedNodes L ρ) = [1, 2, -1] := by
  simp [appendedNodes, pairingBlock, countKind, nodeKind, constList, constOf, List.filterMap_cons]

theorem nodeKind_renameNode {n : NatNode} (hn : n ≠ .var 0) :
    nodeKind (renameNode code n) = nodeKind n := by
  cases n with
  | var i => rcases i with _ | _ | i <;> simp_all [renameNode, nodeKind]
  | _ => rfl

theorem constOf_renameNode {n : NatNode} (hn : n ≠ .var 0) :
    constOf (renameNode code n) = constOf n := by
  cases n with
  | var i => rcases i with _ | _ | i <;> simp_all [renameNode, constOf]
  | _ => rfl

theorem countKind_map_renameNode (κ : NodeKind) {l : List NatNode} (hl : NatNode.var 0 ∉ l) :
    countKind κ (l.map (renameNode code)) = countKind κ l := by
  unfold countKind
  rw [List.countP_map]
  refine List.countP_congr fun n hn => ?_
  simp only [Function.comp, decide_eq_true_eq]
  rw [nodeKind_renameNode code fun h => hl (h ▸ hn)]

theorem constList_map_renameNode {l : List NatNode} (hl : NatNode.var 0 ∉ l) :
    constList (l.map (renameNode code)) = constList l := by
  unfold constList
  rw [List.filterMap_map]
  refine List.filterMap_congr fun n hn => ?_
  exact constOf_renameNode code fun h => hl (h ▸ hn)

theorem countKind_cons (κ : NodeKind) (n : NatNode) (l : List NatNode) :
    countKind κ (n :: l) = (if nodeKind n = κ then 1 else 0) + countKind κ l := by
  simp only [countKind, List.countP_cons, decide_eq_true_eq]
  omega

/-- The node statistics of the specialization in terms of those of `ℋ`. -/
theorem specialize_nodeStats {rest : List NatNode} (hr : H.nodes = .var 0 :: .var 1 :: rest)
    (h0 : NatNode.var 0 ∉ rest) :
    countKind .var (specialize H code).nodes = countKind .var H.nodes - 1 + 8 ∧
    countKind .const (specialize H code).nodes = countKind .const H.nodes + 1 + 3 ∧
    countKind .add (specialize H code).nodes = countKind .add H.nodes + 20 ∧
    countKind .mul (specialize H code).nodes = countKind .mul H.nodes + 21 ∧
    countKind .call (specialize H code).nodes = countKind .call H.nodes ∧
    constList (specialize H code).nodes = code :: constList H.nodes ++ [1, 2, -1] := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := appendedNodes_countKind H.nodes.length H.root
  have h1 : NatNode.var 0 ∉ NatNode.var 1 :: rest := by simpa using h0
  have e1 : ∀ κ, countKind κ (specialize H code).nodes = (if NodeKind.const = κ then 1 else 0) +
      countKind κ (NatNode.var 1 :: rest) + countKind κ (appendedNodes H.nodes.length H.root) :=
    fun κ => by
      simp only [specialize]
      rw [countKind_append, hr, List.map_cons, countKind_cons, countKind_map_renameNode code κ h1]
      rfl
  have e2 : ∀ κ, countKind κ H.nodes =
      (if NodeKind.var = κ then 1 else 0) + countKind κ (NatNode.var 1 :: rest) :=
    fun κ => by rw [hr, countKind_cons]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, e2, a1]; simp
  · rw [e1, e2, a2]; simp; omega
  · rw [e1, e2, a3]; simp
  · rw [e1, e2, a4]; simp
  · rw [e1, e2, a5]; simp
  · simp only [specialize]
    rw [constList_append, a6, hr, List.map_cons, constList, List.filterMap_cons, ← constList,
      constList_map_renameNode code h1]
    simp [renameNode, constOf, constList, List.filterMap_cons]

/-! ### Well-scopedness -/

theorem specialize_wellScoped (hH : H.WellScoped) (hk : H.inputCount = 2)
    {rest : List (ℕ × VarKind)} (hvars : H.explicitVars = (0, .input) :: (1, .input) :: rest) :
    (specialize H code).WellScoped := by
  have hb := specialize_blocks H code
  have hw2 : ∀ w ∈ H.blocks, 2 ≤ w := fun w hw => hk ▸ (hH.block_range w hw).1
  have hmemv : ∀ v ∈ H.explicitVars, 2 ≤ v.1 → (v.1 + 7, v.2) ∈ (specialize H code).explicitVars :=
    fun v hv h2 => by
      rw [hvars] at hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | rfl | hv
      · simp at h2
      · simp at h2
      · simp only [specialize, hvars, List.drop_succ_cons, List.drop_zero, List.mem_append,
          List.mem_map]
        exact Or.inr ⟨v, hv, rfl⟩
  have hnew : ∀ i < 9, ∃ v ∈ (specialize H code).explicitVars, v.1 = i := fun i hi =>
    ⟨(i, if i < 5 then .input else .witness), by simp [specialize, hi], rfl⟩
  refine ⟨fun w hw => ?_, ?_, fun w hw v hv => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hb] at hw
    obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hw
    have := hH.block_range w hw'
    simp only [specialize_inputCount, specialize_varCount]
    omega
  · rw [hb, List.pairwise_map]
    refine hH.blocks_disjoint.imp fun {w w'} h i hi hi' => ?_
    simp only [NatCircuit.InBlock] at hi hi' h
    exact h (i - 7) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · rw [hb] at hw
    obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hw
    have h2 := hw2 w hw'
    simp only [specialize, List.mem_append, List.mem_map, List.mem_range] at hv
    rcases hv with ⟨i, hi, rfl⟩ | ⟨u, hu, rfl⟩
    · simp only [NatCircuit.InBlock]; omega
    · intro hin
      refine hH.blocks_explicit w hw' u (List.mem_of_mem_drop hu) ?_
      simp only [NatCircuit.InBlock] at hin ⊢; omega
  · simp only [specialize_varCount] at hi
    by_cases h9 : i < 9
    · exact Or.inl (hnew i h9)
    · rcases hH.cover (i - 7) (by omega) with ⟨v, hv, hvi⟩ | ⟨w, hw, hwi⟩
      · exact Or.inl ⟨_, hmemv v hv (by omega), by simp only; omega⟩
      · refine Or.inr ⟨w + 7, by rw [hb]; exact List.mem_map_of_mem hw, ?_⟩
        simp only [NatCircuit.InBlock] at hwi ⊢; omega
  · simp only [specialize, List.mem_append, List.mem_map] at hi
    rcases hi with ⟨n, hn, hni⟩ | hi
    · cases n with
      | var j =>
        rcases j with _ | _ | j
        · simp [renameNode] at hni
        · simp only [renameNode, NatNode.var.injEq] at hni
          exact hnew i (by omega)
        · simp only [renameNode, NatNode.var.injEq] at hni
          obtain ⟨v, hv, hvj⟩ := hH.var_explicit _ hn
          exact ⟨_, hmemv v hv (by omega), by simp only; omega⟩
      | const _ => simp [renameNode] at hni
      | add _ _ => simp [renameNode] at hni
      | mul _ _ => simp [renameNode] at hni
      | call _ _ _ _ => simp [renameNode] at hni
    · simp only [appendedNodes, pairingBlock, List.cons_append, List.nil_append, List.mem_cons,
        NatNode.var.injEq, reduceCtorEq, List.not_mem_nil, or_false] at hi
      exact hnew i (by omega)

end ZInQ.Compiler.Universal
