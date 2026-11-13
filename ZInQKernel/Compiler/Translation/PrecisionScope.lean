import ZInQKernel.Compiler.Translation.PowerScope
import ZInQKernel.Compiler.Universal.WrapperCode

/-!
# Scope conditions of the natural precision circuit

The natural precision circuit `𝒩` (the specialization of the universal halting circuit `ℋ` at
the program literal `c₃`) is well-formed with bound `1,305,811`, its `15,845` call nodes calling
the power template `𝒫` (`precisionCircuit_wellFormed`); `𝒫` is well-formed with bound `82` with
explicit variables exactly `0, …, 81` (`powerTemplate_wellFormed`). In particular no variable node
of the parent reads a private coordinate of a power call.

The proof uses the construction: the node list of `ℋ` is well formed (every argument is an
earlier node) by the builder's soundness, its explicit variables lie below its variable count by
the scope invariant, and they are pairwise distinct because together with the `15,845` blocks of
`79` variables they cover the `1,305,804 = 54,049 + 15,845 · 79` variables. The specialization
renames these facts; its `52` appended nodes refer to earlier nodes; its constants are
`c₃, 0, 1, 2, 4, 1399, -1` with `c₃ > 1399`.

(Blueprint: `compiler/translation/precision-circuit-scope.md`.)
-/

namespace ZInQ.Translation

open Compiler.Natural Compiler.Universal Syntax

/-! ### A counting argument for distinctness -/

/-- A list of `n` numbers below `V` that, with `b` intervals of length `m`, covers `[0, V)` with
`n + m b ≤ V` has no repetitions. -/
theorem nodup_of_cover {E B : List ℕ} {m V : ℕ}
    (hcov : ∀ i < V, i ∈ E ∨ ∃ w ∈ B, w ≤ i ∧ i < w + m) (hcount : E.length + m * B.length ≤ V) :
    E.Nodup := by
  classical
  have hsub : Finset.range V ⊆ E.toFinset ∪ B.toFinset.biUnion fun w => Finset.Ico w (w + m) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rcases hcov i hi with h | ⟨w, hw, h1, h2⟩
    · exact Finset.mem_union_left _ (List.mem_toFinset.2 h)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨w, List.mem_toFinset.2 hw,
        Finset.mem_Ico.2 ⟨h1, h2⟩⟩)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_range] at h1
  have h2 := Finset.card_union_le E.toFinset (B.toFinset.biUnion fun w => Finset.Ico w (w + m))
  have h3 : (B.toFinset.biUnion fun w => Finset.Ico w (w + m)).card ≤ m * B.length := by
    refine (Finset.card_biUnion_le).trans ?_
    simp only [Nat.card_Ico, Nat.add_sub_cancel_left, Finset.sum_const, smul_eq_mul]
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ (List.toFinset_card_le B)
  have h4 : E.length ≤ E.toFinset.card := by omega
  rw [List.card_toFinset] at h4
  have := (List.dedup_sublist E).eq_of_length_le h4
  rw [← this]
  exact List.nodup_dedup E

/-! ### The halting circuit -/

theorem haltingCircuit_nodesWF : NodesWF haltingCircuit.nodes := by
  have hP : ∀ x ∈ inputs 2, x.Valid ExPoly.empty (State.init 2) := fun x hx => by
    simp only [inputs, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact input_valid hi
  obtain ⟨h1, -, h3⟩ := Compiler.Packed.triple_construction (T := ExPoly.empty) interpreter 204 2
    (State.init 2) (init_nodesWF 2) hP
  have h := (encode_correct _ _ h1 h3).1
  rw [haltingCircuit, Compiler.Packed.compiled, NM.toCircuit_nodes]
  exact h

theorem haltingCircuit_vars_lt : ∀ v ∈ haltingCircuit.explicitVars, v.1 < haltingCircuit.varCount := by
  have h := Pres.encode (k := 2) ExPoly.empty
    (Compiler.Packed.construction interpreter 204 2 (State.init 2)).1 _
    (Compiler.Packed.pres_construction interpreter 204 _ (scopeInv_init 2))
  rw [haltingCircuit, Compiler.Packed.compiled, NM.toCircuit_explicitVars, NM.toCircuit_varCount]
  exact h.vars_lt

theorem haltingCircuit_vars_nodup : (haltingCircuit.explicitVars.map Prod.fst).Nodup := by
  obtain ⟨-, hv, hb, -, hn, hws⟩ := haltingCircuit_counts
  refine nodup_of_cover (B := haltingCircuit.blocks) (m := 79) (V := haltingCircuit.varCount)
    (fun i hi => ?_) (by rw [List.length_map, hv, hb, hn])
  rcases hws.cover i hi with ⟨v, hv, rfl⟩ | ⟨w, hw, h⟩
  · exact Or.inl (List.mem_map.2 ⟨v, hv, rfl⟩)
  · exact Or.inr ⟨w, hw, h⟩

/-! ### The specialization -/

theorem children_renameNode (code : ℤ) (n : NatNode) :
    (renameNode code n).children = n.children := by
  cases n with
  | var i => rcases i with _ | _ | i <;> rfl
  | _ => rfl

theorem appendedNodes_length (L ρ : ℕ) : (appendedNodes L ρ).length = 52 := rfl

theorem appendedNodes_wf {L ρ : ℕ} (hρ : ρ < L) (t : ℕ) (ht : t < 52) :
    ∀ i ∈ ((appendedNodes L ρ)[t]'(by rw [appendedNodes_length]; exact ht)).children, i < L + t := by
  interval_cases t <;> (simp [appendedNodes, pairingBlock, NatNode.children]; try omega)

theorem specialize_nodesWF {H : NatCircuit} (hH : NodesWF H.nodes) (hρ : H.root < H.nodes.length)
    (code : ℤ) : NodesWF (specialize H code).nodes := by
  have hn : (specialize H code).nodes =
      H.nodes.map (renameNode code) ++ appendedNodes H.nodes.length H.root := rfl
  intro j hj i hi
  have hj' := hj
  rw [specialize_nodes_length] at hj'
  simp only [hn] at hi
  rcases Nat.lt_or_ge j H.nodes.length with hjL | hjL
  · rw [List.getElem_append_left (by simpa using hjL), List.getElem_map, children_renameNode]
      at hi
    exact hH j hjL i hi
  · rw [List.getElem_append_right (by simpa using hjL)] at hi
    simp only [List.length_map] at hi
    have ht : j - H.nodes.length < 52 := by omega
    have := appendedNodes_wf hρ _ ht i hi
    omega

theorem specialize_root_lt (H : NatCircuit) (code : ℤ) :
    (specialize H code).root < (specialize H code).nodes.length := by
  rw [specialize_nodes_length]
  show H.nodes.length + 51 < H.nodes.length + 52
  omega

/-- Conditions 1–6 for the precision circuit at a literal `code ≥ 2`. -/
theorem precisionCircuitOf_core {code : ℤ} (hc : 2 ≤ code) :
    WellFormedCore (precisionCircuitOf code) 79 1305811 := by
  obtain ⟨rest, hr, hw, he⟩ := precisionCircuitOf_explicitVars code
  have hws := precisionCircuitOf_wellScoped code
  have hV := (precisionCircuitOf_counts code).2.2.2.1
  have hnd := haltingCircuit_vars_nodup
  rw [hr] at hnd
  simp only [List.map_cons, List.nodup_cons, List.mem_cons, List.mem_map, not_or] at hnd
  obtain ⟨⟨h01, h0r⟩, h1r, hrnd⟩ := hnd
  have hrest2 : ∀ v ∈ rest, 2 ≤ v.1 := fun v hv => by
    have a : v.1 ≠ 0 := fun h => h0r ⟨v, hv, h⟩
    have b : v.1 ≠ 1 := fun h => h1r ⟨v, hv, h⟩
    omega
  have hrlt : ∀ v ∈ rest, v.1 + 7 < 1305811 := fun v hv => by
    have := haltingCircuit_vars_lt v (by rw [hr]; simp [hv])
    rw [haltingCircuit_counts.2.2.2.2.1] at this
    omega
  refine ⟨?_, ?_, ?_, ?_, specialize_nodesWF haltingCircuit_nodesWF haltingCircuit_root_lt code,
    specialize_root_lt _ code,
    hws.var_explicit, fun c hcn h0 h1 h2 => ?_, ?_, fun w hw' v hv => ?_, fun v hv => ?_,
    fun w hw' i hi => ?_⟩
  · rw [he, List.map_append, List.map_map]
    have hmap : rest.map ((fun v : ℕ × VarKind => v.1) ∘ fun v => (v.1 + 7, v.2)) =
        (rest.map Prod.fst).map (· + 7) := by simp [List.map_map, Function.comp_def]
    rw [hmap]
    refine List.nodup_append.2 ⟨by decide, hrnd.map (add_left_injective 7), ?_⟩
    · intro a ha b hb
      rw [List.map_map] at hb
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hb
      have := hrest2 v hv
      simp at ha
      show a ≠ v.1 + 7
      omega
  · rw [he]; rfl
  · rw [he]; show 5 ≤ _; simp
  · intro v hv
    rw [he, List.drop_append_of_le_length (by show 5 ≤ 9; norm_num), List.mem_append] at hv
    rcases hv with hv | hv
    · have hv' : v ∈ [((5 : ℕ), VarKind.witness), (6, .witness), (7, .witness), (8, .witness)] :=
        hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
      rcases hv' with rfl | rfl | rfl | rfl <;> rfl
    · obtain ⟨v', hv', rfl⟩ := List.mem_map.1 hv
      exact hw v' hv'
  · have := precisionCircuitOf_consts code hcn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    omega
  · refine hws.blocks_disjoint.imp fun h i hi hi' => h i hi hi'
  · exact hws.blocks_explicit w hw' v hv
  · rw [he] at hv
    simp only [List.mem_append, List.mem_map] at hv
    rcases hv with hv | ⟨v', hv', rfl⟩
    · simp at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    · exact hrlt v' hv'
  · have := (hws.block_range w hw').2
    rw [hV] at this
    simp only [InBlock] at hi
    simp only [powerWitnesses] at this
    omega

/-- **Scope conditions of the natural precision circuit.** `𝒩` is well-formed with bound
`1,305,811` with power template `𝒫`, and has `15,845` call nodes; `𝒫` is well-formed with bound
`82`, its explicit variables being `0, 1, …, 81`. -/
theorem precisionCircuit_wellFormed :
    WellFormed powerTemplateCircuit precisionCircuit 1305811 ∧
      precisionCircuit.blocks.length = 15845 ∧
      WellFormed powerTemplateCircuit powerTemplateCircuit 82 ∧
      powerTemplateCircuit.explicitVars.map Prod.fst = List.range 82 := by
  obtain ⟨hP, hPe, hPi, hPv, hPc, hPcore⟩ := powerTemplate_wellFormed
  refine ⟨⟨?_, fun _ => ⟨hPi, hPc, hPcore, by rw [hPv]; exact hPe⟩⟩,
    (precisionCircuitOf_counts c3).2.2.1, hP, hPe⟩
  rw [hPv]
  exact precisionCircuitOf_core (by have := c3_gt; omega)

end ZInQ.Translation
