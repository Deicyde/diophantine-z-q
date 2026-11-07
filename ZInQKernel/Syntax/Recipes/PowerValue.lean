import ZInQKernel.Syntax.Recipes.Translate

/-!
# The power-value recipe

Blueprint: `syntax/recipes/recipe-power-value.md`.

`power_value` is the translation of the power template of the natural precision polynomial
(`ZInQ.Compiler.Natural.powerTemplateCircuit`: `3` inputs, `79` witnesses, explicit variables
`0, …, 81`) in value mode, without natural constraints on the inputs and without a power recipe.
Its constants `4, 2, 3` are, in order of first occurrence, the first three entries of the
constant table, so they become `integer_constant_0, 1, 2` (templates `18, 19, 20`).

Its counts follow from the closed form of the translation count and the node statistics of the
power template, a kernel computation on its `474` nodes (`powerTemplateCircuit_translationStats`):
`20` parameters and `20 + 3 + 79(5 + 140604) + 3(5 + 1) + 196(5 + 6) + 190(5 + 35134) = 17786718`
variables.
-/

namespace ZInQ.Syntax

open ZInQ.Compiler.Natural

/-- The constant table after the translation of the power template: `4, 2, 3`. -/
def powerConstants : List ℤ := [4, 2, 3]

/-- **The power-value recipe.** -/
noncomputable def powerValueRecipe : ModelRecipe :=
  translate powerConstants powerTemplateCircuit .value false none

set_option maxRecDepth 100000 in
/-- The statistics of the power template that the translation count needs: every explicit
variable after the three inputs is a witness (`79` of them), `196` additions, `190`
multiplications and no calls, and the nontrivial constants `4, 2, 3` in node order. A kernel
computation on the `474` nodes. -/
theorem powerTemplateCircuit_translationStats :
    (powerTemplateCircuit.explicitVars.map (varCost 3 false)).sum = 79 * (5 + 140604) ∧
      (powerTemplateCircuit.nodes.map (nodeCost 0)).sum = 196 * (5 + 6) + 190 * (5 + 35134) ∧
      powerTemplateCircuit.nodes.filterMap nontrivialConst = [4, 2, 3] := by
  decide +kernel

theorem powerValueRecipe_parameterCount : powerValueRecipe.parameterCount = 20 := rfl

/-- `power_value` has `17786718` variables, hence `17786698` witnesses. -/
theorem powerValueRecipe_variableCount : powerValueRecipe.variableCount = 17786718 := by
  obtain ⟨h1, h2, h3⟩ := powerTemplateCircuit_translationStats
  rw [powerValueRecipe, translate_variableCount]
  simp only [NM.toCircuit_inputCount, powerTemplateCircuit, Option.map_none, Option.getD_none]
  simp only [powerTemplateCircuit] at h1 h2 h3
  rw [h1, h2, h3]
  rfl

end ZInQ.Syntax
