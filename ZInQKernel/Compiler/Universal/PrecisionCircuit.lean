import ZInQKernel.Compiler.Universal.SpecializeShape
import ZInQKernel.Compiler.NodeBound.Defs

/-!
# The five-input natural precision circuit

The natural precision circuit is the specialization of the universal halting circuit `ℋ` at the
program literal `c₃` (`specialize`). This module states its properties for an arbitrary literal
`code`, as `precisionCircuitOf code`; the precision circuit itself is `precisionCircuitOf c₃` with
`c₃ = code(𝒲)` the code of the wrapper (`WrapperCode.lean`).

1. Its polynomial is `θ([[ℋ]])² + Σ_{i<4} π_i²` and, for natural `code`, its natural zeros at
   `c ∈ ℕ⁵` are the natural zeros of `ℋ` at `(code, enc₅(c))`.
2. It is well scoped.
3. Shape: `5` inputs, `54,056` explicit variables, `15,845` calls, variable count `1,305,811`;
   given the node check of `ℋ`, `293,620` nodes (`54,056` variable, `10` constant, `125,327`
   addition, `98,382` multiplication, `15,845` call nodes) with constants
   `code, 0, 1, 2, 4, 1399, -1, 1, 2, -1` in node order. Given only the addition and
   multiplication bound of `ℋ` (`NodeCheck.HaltingAddMulBound`), at most `125,327` addition and
   `98,382` multiplication nodes (`precisionCircuitOf_addMulBound`).

(Blueprint: `compiler/natural/universal/precision-circuit.md`,
`precision-circuit-specialization.md`, `circuit-node-counts.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Universal

open Natural Syntax MvPolynomial Packed

/-- The five-input natural precision circuit at the program literal `code`. -/
def precisionCircuitOf (code : ℤ) : NatCircuit := specialize haltingCircuit code

/-! ### Facts about the halting circuit used by the specialization -/

theorem haltingCircuit_root_lt : haltingCircuit.root < haltingCircuit.nodes.length := by
  have hP : ∀ x ∈ inputs 2, x.Valid ExPoly.empty (State.init 2) := fun x hx => by
    simp only [inputs, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact input_valid hi
  obtain ⟨h1, -, h3⟩ := triple_construction (T := ExPoly.empty) interpreter 204 2 (State.init 2)
    (init_nodesWF 2) hP
  have h := (encode_correct _ _ h1 h3).2.2.1.1
  rw [haltingCircuit, compiled, NM.toCircuit_root, NM.toCircuit_nodes]
  exact h

theorem haltingCircuit_call_ge {a b c w : ℕ} (h : NatNode.call a b c w ∈ haltingCircuit.nodes) :
    2 ≤ w := by
  have hw : w ∈ haltingCircuit.blocks := by
    rw [blocks_eq_filterMap]
    exact List.mem_filterMap.2 ⟨_, h, rfl⟩
  exact (haltingCircuit_counts.2.2.2.2.2.block_range w hw).1

/-- The node list of `ℋ` is `var 0 :: var 1 :: rest` with no other node `var 0`. -/
theorem haltingCircuit_nodes_eq' :
    ∃ rest, haltingCircuit.nodes = .var 0 :: .var 1 :: rest ∧ NatNode.var 0 ∉ rest := by
  obtain ⟨rest, hr⟩ := haltingCircuit_nodes_eq
  refine ⟨rest, hr, fun h => ?_⟩
  have hnd := haltingCircuit_nonCall_nodup
  rw [hr] at hnd
  change (NatNode.var 0 :: nonCall (NatNode.var 1 :: rest)).Nodup at hnd
  exact (List.nodup_cons.1 hnd).1 (List.mem_filter.2 ⟨List.mem_cons_of_mem _ h, rfl⟩)

theorem haltingCircuit_varCount_ge : 2 ≤ haltingCircuit.varCount := by
  rw [haltingCircuit_counts.2.2.2.2.1]; norm_num

/-! ### Polynomial and natural relation -/

/-- **The precision circuit is a specialization**: `[[𝒩]] = θ([[ℋ]])² + Σ_{i<4} π_i²`. -/
theorem precisionCircuitOf_poly (code : ℤ) (T : ExPoly) :
    (precisionCircuitOf code).poly T =
      bind₁ (theta code) (haltingCircuit.poly T) ^ 2 + ∑ i : Fin 4, pairPoly i ^ 2 :=
  specialize_poly _ _ _ haltingCircuit_nodes_eq haltingCircuit_root_lt
    fun _ _ _ _ h => haltingCircuit_call_ge h

/-- **The precision circuit is a specialization**: for natural `code` and `c ∈ ℕ⁵`,
`Z_𝒩(c) ↔ Z_ℋ(code, enc₅(c))`. -/
theorem precisionCircuitOf_natRel_iff (code : ℕ) (T : ExPoly) (c : Fin 5 → ℕ) :
    (precisionCircuitOf code).NatRel T c ↔
      haltingCircuit.NatRel T ![code, CantorDecoder.encode5 (c 0) (c 1) (c 2) (c 3) (c 4)] := by
  refine (specialize_natRel_iff _ code T haltingCircuit_nodes_eq haltingCircuit_root_lt
    (fun _ _ _ _ h => haltingCircuit_call_ge h) haltingCircuit_varCount_ge c).trans ?_
  refine Iff.symm ((natRel_iff_point haltingCircuit T (by
    rw [haltingCircuit_inputCount]; exact haltingCircuit_varCount_ge) _).trans ?_)
  refine exists_congr fun y => ?_
  constructor
  · rintro ⟨hin, hz, h⟩
    exact ⟨(hin 0 (by decide)).trans rfl, (hin 1 (by decide)).trans rfl, hz, h⟩
  · rintro ⟨h0, h1, hz, h⟩
    refine ⟨fun i hi => ?_, hz, h⟩
    change i < 2 at hi
    rcases i with _ | _ | i
    · exact h0.trans rfl
    · exact h1.trans rfl
    · omega

/-- **The precision circuit is well scoped.** -/
theorem precisionCircuitOf_wellScoped (code : ℤ) : (precisionCircuitOf code).WellScoped := by
  obtain ⟨rest, hr⟩ := haltingCircuit_explicitVars_eq
  exact specialize_wellScoped _ _ haltingCircuit_counts.2.2.2.2.2 rfl hr

/-! ### Shape -/

/-- **Counts of the precision circuit**: `5` inputs, `54,056` explicit variables, `15,845` calls
with blocks of `79`, variable count `1,305,811`, hence `1,305,806` witness coordinates. -/
theorem precisionCircuitOf_counts (code : ℤ) :
    (precisionCircuitOf code).inputCount = 5 ∧
    (precisionCircuitOf code).explicitVars.length = 54056 ∧
    (precisionCircuitOf code).blocks.length = 15845 ∧
    (precisionCircuitOf code).varCount = 1305811 ∧
    (precisionCircuitOf code).varCount - (precisionCircuitOf code).inputCount = 1305806 := by
  obtain ⟨-, hv, hb, -, hn, -⟩ := haltingCircuit_counts
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [precisionCircuitOf, specialize_explicitVars_length, hv]
  · rw [precisionCircuitOf, specialize_blocks_length, hb]
  · rw [precisionCircuitOf, specialize_varCount, hn]
  · rw [precisionCircuitOf, specialize_varCount, hn]; rfl

/-- The explicit variables of the precision circuit: `0, …, 8` (the first five inputs), then the
explicit witnesses of `ℋ` shifted by `7` (so `5` inputs and `54,051` witnesses). -/
theorem precisionCircuitOf_explicitVars (code : ℤ) :
    ∃ rest, haltingCircuit.explicitVars = (0, .input) :: (1, .input) :: rest ∧
      (∀ v ∈ rest, v.2 = .witness) ∧
      (precisionCircuitOf code).explicitVars =
        [(0, .input), (1, .input), (2, .input), (3, .input), (4, .input), (5, .witness),
          (6, .witness), (7, .witness), (8, .witness)] ++ rest.map fun v => (v.1 + 7, v.2) := by
  obtain ⟨rest, hr, hw⟩ := haltingCircuit_explicitVars_eq'
  refine ⟨rest, hr, hw, ?_⟩
  simp [precisionCircuitOf, specialize, hr, List.range_succ]

/-- **Shape of the natural precision circuit**, node statistics: from the node check of `ℋ`,
`293,620` nodes, `54,056` variable nodes, `10` constant nodes with values
`code, 0, 1, 2, 4, 1399, -1, 1, 2, -1`, `125,327` additions, `98,382` multiplications and
`15,845` calls. -/
theorem precisionCircuitOf_nodeStats (hN : HaltingNodeCheck) (code : ℤ) :
    (precisionCircuitOf code).nodes.length = 293620 ∧
    countKind .var (precisionCircuitOf code).nodes = 54056 ∧
    countKind .const (precisionCircuitOf code).nodes = 10 ∧
    countKind .add (precisionCircuitOf code).nodes = 125327 ∧
    countKind .mul (precisionCircuitOf code).nodes = 98382 ∧
    countKind .call (precisionCircuitOf code).nodes = 15845 ∧
    constList (precisionCircuitOf code).nodes = [code, 0, 1, 2, 4, 1399, -1, 1, 2, -1] := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, -, -⟩ := haltingCircuit_nodeStats hN
  obtain ⟨rest, hr, h0⟩ := haltingCircuit_nodes_eq'
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := specialize_nodeStats haltingCircuit code hr h0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [precisionCircuitOf, specialize_nodes_length, hl]
  · rw [precisionCircuitOf, k1, h1]
  · rw [precisionCircuitOf, k2, h2]
  · rw [precisionCircuitOf, k3, h3]
  · rw [precisionCircuitOf, k4, h4]
  · rw [precisionCircuitOf, k5, h5]
  · rw [precisionCircuitOf, k6, h6]; rfl

/-- **Shape of the natural precision circuit**, addition and multiplication bounds: from the
bound of `ℋ`, at most `125,327` additions and `98,382` multiplications. -/
theorem precisionCircuitOf_addMulBound (hB : NodeCheck.HaltingAddMulBound) (code : ℤ) :
    countKind .add (precisionCircuitOf code).nodes ≤ 125327 ∧
    countKind .mul (precisionCircuitOf code).nodes ≤ 98382 := by
  obtain ⟨h3, h4⟩ := hB
  obtain ⟨rest, hr, h0⟩ := haltingCircuit_nodes_eq'
  obtain ⟨-, -, k3, k4, -, -⟩ := specialize_nodeStats haltingCircuit code hr h0
  refine ⟨?_, ?_⟩
  · rw [precisionCircuitOf, k3]; omega
  · rw [precisionCircuitOf, k4]; omega

/-- The number of call nodes of the precision circuit; this needs no node check. -/
theorem precisionCircuitOf_countKind_call (code : ℤ) :
    countKind .call (precisionCircuitOf code).nodes = 15845 := by
  obtain ⟨rest, hr, h0⟩ := haltingCircuit_nodes_eq'
  obtain ⟨-, -, -, -, k5, -⟩ := specialize_nodeStats haltingCircuit code hr h0
  rw [precisionCircuitOf, k5, haltingCircuit_countKind_call]

/-- The constants of the precision circuit are among `code, 0, 1, 2, 4, 1399, -1`; this needs no
node check. -/
theorem precisionCircuitOf_consts (code : ℤ) {c : ℤ}
    (h : NatNode.const c ∈ (precisionCircuitOf code).nodes) :
    c ∈ ({code, 0, 1, 2, 4, 1399, -1} : Set ℤ) := by
  simp only [precisionCircuitOf, specialize, List.mem_append, List.mem_map] at h
  rcases h with ⟨n, hn, hnc⟩ | h
  · cases n with
    | const c' =>
      simp only [renameNode, NatNode.const.injEq] at hnc
      subst hnc
      have := haltingCircuit_consts hn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
      omega
    | var i =>
      rcases i with _ | _ | i
      · simp only [renameNode, NatNode.const.injEq] at hnc
        subst hnc; simp
      · simp [renameNode] at hnc
      · simp [renameNode] at hnc
    | add _ _ => simp [renameNode] at hnc
    | mul _ _ => simp [renameNode] at hnc
    | call _ _ _ _ => simp [renameNode] at hnc
  · simp only [appendedNodes, pairingBlock, List.cons_append, List.nil_append, List.mem_cons,
      NatNode.const.injEq, reduceCtorEq, List.not_mem_nil, or_false, false_or] at h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega

/-- The constants of the precision circuit other than `0, 1, -1` are, in order of first
occurrence, `code, 2, 4, 1399`; for `1399 < code` these four values are distinct. -/
theorem precisionCircuitOf_constants (hN : HaltingNodeCheck) (code : ℤ) (hc : 1399 < code) :
    (∀ v ∈ constList (precisionCircuitOf code).nodes, v ∈ ({0, 1, -1, code, 2, 4, 1399} : Set ℤ)) ∧
    [code, (2 : ℤ), 4, 1399].Nodup := by
  rw [(precisionCircuitOf_nodeStats hN code).2.2.2.2.2.2]
  refine ⟨fun v hv => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · refine List.nodup_cons.2 ⟨?_, by decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega

end ZInQ.Compiler.Universal
