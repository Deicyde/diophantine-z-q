import ZInQKernel.Compiler.Translation.WellFormed
import ZInQKernel.Compiler.Circuits.PowerTemplateNodes

/-!
# Scope of the power template

The power template `𝒫` is well-formed with bound `82`, its explicit variables being exactly
`0, 1, …, 81` in increasing order with `0, 1, 2` the inputs, and it has no call nodes
(`powerTemplate_wellFormed`). The finite facts are one kernel computation on its `474` nodes
(`powerTemplateCheck`).

(Blueprint: `compiler/translation/precision-circuit-scope.md`, the power-template part.)
-/

namespace ZInQ.Translation

open Compiler.Natural Syntax

/-- The node conditions of the power template: arguments are earlier nodes, variables below
`82`, constants trivial or at least `2`, no call nodes. -/
def powerNodeOK (j : ℕ) : NatNode → Bool
  | .var i => decide (i < 82)
  | .const c => decide (c = 0 ∨ c = 1 ∨ c = -1 ∨ 2 ≤ c)
  | .add a b => decide (a < j ∧ b < j)
  | .mul a b => decide (a < j ∧ b < j)
  | .call _ _ _ _ => false

/-- The finite check of the power template, a Boolean function of its node list. -/
noncomputable def powerTemplateCheck : Bool :=
  (powerTemplateCircuit.nodes.zipIdx.all fun e => powerNodeOK e.2 e.1) &&
    decide (powerTemplateCircuit.root < powerTemplateCircuit.nodes.length) &&
    (powerTemplateCircuit.explicitVars ==
      (List.range 82).map (fun i => (i, if i < 3 then VarKind.input else VarKind.witness)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check holds (a kernel computation on the `474` nodes). -/
theorem powerTemplateCheck_eq_true : powerTemplateCheck = true := by
  decide +kernel

theorem powerTemplate_node_ok {j : ℕ} (hj : j < powerTemplateCircuit.nodes.length) :
    powerNodeOK j powerTemplateCircuit.nodes[j] = true := by
  have h := powerTemplateCheck_eq_true
  simp only [powerTemplateCheck, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1 (powerTemplateCircuit.nodes[j], j)
    (List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hj))

theorem powerTemplate_root_lt : powerTemplateCircuit.root < powerTemplateCircuit.nodes.length := by
  have h := powerTemplateCheck_eq_true
  simp only [powerTemplateCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem powerTemplate_explicitVars : powerTemplateCircuit.explicitVars =
    (List.range 82).map (fun i => (i, if i < 3 then VarKind.input else VarKind.witness)) := by
  have h := powerTemplateCheck_eq_true
  simp only [powerTemplateCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem powerTemplate_no_call (a b c w : ℕ) : NatNode.call a b c w ∉ powerTemplateCircuit.nodes := by
  intro h
  obtain ⟨j, hj, hjn⟩ := List.mem_iff_getElem.1 h
  have := powerTemplate_node_ok hj
  rw [hjn] at this
  simp [powerNodeOK] at this

theorem powerTemplate_blocks : powerTemplateCircuit.blocks = [] := by
  unfold NatCircuit.blocks
  rw [List.filterMap_eq_nil_iff]
  intro n hn
  cases n with
  | call a b c w => exact absurd hn (powerTemplate_no_call a b c w)
  | _ => rfl

theorem powerTemplate_inputCount : powerTemplateCircuit.inputCount = 3 := rfl

/-- Conditions 1–6 for the power template, with any block length and bound `82`. -/
theorem powerTemplate_core (m : ℕ) : WellFormedCore powerTemplateCircuit m 82 := by
  have hev := powerTemplate_explicitVars
  refine ⟨?_, ?_, ?_, ?_, fun j hj i hi => ?_, powerTemplate_root_lt, fun i hi => ?_,
    fun c hc h0 h1 h2 => ?_, by rw [powerTemplate_blocks]; exact List.Pairwise.nil,
    by rw [powerTemplate_blocks]; simp, fun v hv => ?_, by rw [powerTemplate_blocks]; simp⟩
  · rw [hev, List.map_map]
    have : (Prod.fst ∘ fun i => (i, if i < 3 then VarKind.input else VarKind.witness)) = id :=
      rfl
    rw [this, List.map_id]
    exact List.nodup_range
  · rw [hev, powerTemplate_inputCount]; decide
  · rw [hev, powerTemplate_inputCount]; simp
  · rw [hev, powerTemplate_inputCount]; decide
  · have := powerTemplate_node_ok hj
    generalize powerTemplateCircuit.nodes[j] = n at this hi
    cases n <;> simp_all [powerNodeOK, NatNode.children] <;> omega
  · obtain ⟨j, hj, hjn⟩ := List.mem_iff_getElem.1 hi
    have := powerTemplate_node_ok hj
    rw [hjn] at this
    simp only [powerNodeOK, decide_eq_true_eq] at this
    exact ⟨_, by rw [hev]; exact List.mem_map.2 ⟨i, List.mem_range.2 this, rfl⟩, rfl⟩
  · obtain ⟨j, hj, hjn⟩ := List.mem_iff_getElem.1 hc
    have := powerTemplate_node_ok hj
    rw [hjn] at this
    simp only [powerNodeOK, decide_eq_true_eq] at this
    omega
  · rw [hev] at hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    exact List.mem_range.1 hi

/-- **Scope of the power template.** `𝒫` has `3` inputs, explicit variables exactly
`0, 1, …, 81` in increasing order, no call nodes, and is well-formed with bound `82` (as its own
power template, and as the power template of a circuit, with blocks of `79` variables). -/
theorem powerTemplate_wellFormed :
    WellFormed powerTemplateCircuit powerTemplateCircuit 82 ∧
      powerTemplateCircuit.explicitVars.map Prod.fst = List.range 82 ∧
      powerTemplateCircuit.inputCount = 3 ∧ powerTemplateCircuit.varCount = 82 ∧
      (∀ a b c w, NatNode.call a b c w ∉ powerTemplateCircuit.nodes) ∧
      WellFormedCore powerTemplateCircuit 0 powerTemplateCircuit.varCount := by
  have hev : powerTemplateCircuit.explicitVars.map Prod.fst = List.range 82 := by
    rw [powerTemplate_explicitVars, List.map_map]
    exact List.map_id _
  refine ⟨⟨powerTemplate_core _, fun ⟨a, b, c, w, h⟩ => absurd h (powerTemplate_no_call a b c w)⟩,
    hev, rfl, powerTemplateCircuit_varCount, powerTemplate_no_call, ?_⟩
  rw [powerTemplateCircuit_varCount]
  exact powerTemplate_core 0

end ZInQ.Translation
