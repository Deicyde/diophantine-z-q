import ZInQKernel.Syntax.Recipes.PowerValue

/-!
# The precision recipe

Blueprint: `syntax/recipes/recipe-precision.md`.

`precision` is the translation of the five-input natural precision circuit `N` in zero mode,
with natural constraints on the inputs and with power recipe `power_value` (recipe index `0`,
witness count `17786698`), performed after the translation of the power template: the constant
table is `integerConstants c₃ = [4, 2, 3, c₃, 1399]`, so `4, 2, 3` keep their indices `0, 1, 2`
and `c₃`, `1399` become `integer_constant_3`, `integer_constant_4`.

The circuit `N` and the program literal `c₃` are parameters (the compiler chapter constructs
them). The count needs only the shape of `N` (`PrecisionShape`): `5` inputs, at most `54056`
explicit variables of which the first five are the inputs, at most `125327` additions, `98382`
multiplications and `15845` calls, and nontrivial constants among `c₃, 2, 4, 1399`. Then
`precision` has at most `292889492861` variables (`precisionRecipe_variableCount_le`); with the
exact shape it has exactly that many.
-/

namespace ZInQ.Syntax

open ZInQ.Compiler.Natural

/-- **The precision recipe** of the natural precision circuit `N` with program literal `c₃`. -/
noncomputable def precisionRecipe (N : NatCircuit) (c3 : ℤ) : ModelRecipe :=
  translate (integerConstants c3) N .zero true
    (some (0, powerValueRecipe.variableCount - powerValueRecipe.parameterCount))

theorem precisionRecipe_parameterCount (N : NatCircuit) (c3 : ℤ) :
    (precisionRecipe N c3).parameterCount = 5 * N.inputCount := rfl

/-- Addition and multiplication nodes. -/
def NatNode.isAdd : NatNode → Bool
  | .add _ _ => true
  | _ => false

/-- Multiplication nodes. -/
def NatNode.isMul : NatNode → Bool
  | .mul _ _ => true
  | _ => false

/-- The shape of the natural precision circuit used by the witness accounting (items 2–4 of
the compiler chapter's `circuit-node-counts`, as upper bounds). -/
structure PrecisionShape (N : NatCircuit) (c3 : ℤ) : Prop where
  inputCount : N.inputCount = 5
  explicitVars_length : N.explicitVars.length ≤ 54056
  inputs : 5 ≤ N.explicitVars.countP fun v => decide (IsInputVar 5 v)
  adds : N.nodes.countP NatNode.isAdd ≤ 125327
  muls : N.nodes.countP NatNode.isMul ≤ 98382
  calls : N.nodes.countP NatNode.isCall ≤ 15845
  consts : ∀ c ∈ N.nodes.filterMap nontrivialConst, c = c3 ∨ c = 2 ∨ c = 4 ∨ c = 1399

theorem sum_varCost_true (k : ℕ) (l : List (ℕ × VarKind)) :
    (l.map (varCost k true)).sum + 5 * l.countP (fun v => decide (IsInputVar k v)) =
      (5 + 140604) * l.length := by
  induction l with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, List.length_cons]
    by_cases hv : IsInputVar k v
    · simp [varCost, hv]
      omega
    · simp [varCost, hv]
      omega

theorem sum_nodeCost (W : ℕ) (l : List NatNode) :
    (l.map (nodeCost W)).sum = (5 + 6) * l.countP NatNode.isAdd +
      (5 + 35134) * l.countP NatNode.isMul + (5 + W) * l.countP NatNode.isCall := by
  induction l with
  | nil => simp
  | cons n l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    cases n <;> simp [nodeCost, NatNode.isAdd, NatNode.isMul, NatNode.isCall, ih] <;> ring

theorem card_le_of_forall_mem {c3 : ℤ} {l : List ℤ}
    (h : ∀ c ∈ l, c = c3 ∨ c = 2 ∨ c = 4 ∨ c = 1399) : l.toFinset.card ≤ 4 := by
  have hsub : l.toFinset ⊆ {c3, 2, 4, 1399} := by
    intro c hc
    rw [List.mem_toFinset] at hc
    simpa using h c hc
  exact (Finset.card_le_card hsub).trans (Finset.card_le_four)

/-- **The count of the precision recipe**: at most `292889492861` variables, hence at most
`292889492836` witnesses. -/
theorem precisionRecipe_variableCount_le {N : NatCircuit} {c3 : ℤ} (hN : PrecisionShape N c3) :
    (precisionRecipe N c3).variableCount ≤ 292889492861 := by
  rw [precisionRecipe, translate_variableCount]
  simp only [Option.map_some, Option.getD_some, powerValueRecipe_variableCount,
    powerValueRecipe_parameterCount, hN.inputCount, trParams]
  have h1 := sum_varCost_true 5 N.explicitVars
  have h2 := sum_nodeCost (17786718 - 20) N.nodes
  have h3 := card_le_of_forall_mem hN.consts
  have := hN.explicitVars_length
  have := hN.inputs
  have := hN.adds
  have := hN.muls
  have := hN.calls
  omega

end ZInQ.Syntax
