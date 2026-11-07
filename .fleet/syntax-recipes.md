# syntax-recipes: report

Recipes of the specification and the specified polynomial (blueprint `syntax/recipes/`,
`syntax/fixed-scalar-semantics.md`, `syntax/literal-polynomial.md`). Directory
`ZInQKernel/Syntax/Recipes/`, root module `ZInQKernel/Syntax/Recipes.lean`. `lake build ZInQKernel`
succeeds. No `sorry`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound` (checked with
`#print axioms` on the main theorems). Branch `wip/nat-halting` is merged.

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| syntax/fixed-scalar-semantics.md | `ZInQ.Syntax.scalarTemplate_rel_iff_pointCode`, `ZInQ.Syntax.scalarTemplate_rel_iff_iota` (FixedScalar.lean) | proved |
| syntax/recipes/recipe-power-value.md | `ZInQ.Syntax.powerValueRecipe`, `powerValueRecipe_parameterCount` (20), `powerValueRecipe_variableCount` (17786718) (PowerValue.lean) | proved |
| syntax/recipes/model-evaluation-translation.md | `ZInQ.Syntax.translate` (+ `TrState`, `trVar`, `trNode`, `OutputMode`), `translate_variableCount` (Translate.lean) | proved |
| syntax/recipes/outer-recipes.md | `ZInQ.Syntax.closeRecipe`, `mainRecipe`, `valueUnionRecipe`, `valueRecipe`, `integersRecipe`, with `*_calls`, `*_fresh`, `*_variableCount` (Outer.lean) | proved |
| syntax/recipes/template-witness-counts.md | `ZInQ.Syntax.templateLibrary_params`, `templateLibrary_witnesses` (already on main); added `templateLibrary_getEx_witnesses` | proved |
| syntax/recipes/witness-count-identity.md | `ZInQ.Syntax.witness_count_arith`, `variable_count_arith` (Arith.lean, by `decide`) | proved |
| syntax/recipes/recipe-precision.md | `ZInQ.Syntax.precisionRecipe N c3`, `precisionRecipe_variableCount_le` (Precision.lean) | proved (circuit and `c₃` as parameters) |
| syntax/recipes/witness-accounting.md | `ZInQ.Syntax.specRecipes`, `specLib`, `specLib_wf`, `specIntegers_variableCount_eq`, `specIntegers_variableCount_le`, `vars_integers_lt` (Accounting.lean) | proved (as upper bounds, see below) |
| syntax/recipes/fin-variable-form.md | `ZInQ.Syntax.PstarOf_spec`, `PstarOf_zero_projection`, `Pstar_spec`, `Pstar_zero_projection`, `specPstar_spec`, `specPstar_zero_projection` (Polynomial.lean, Literal.lean) | proved |
| syntax/literal-polynomial.md | `ZInQ.Syntax.PstarNatOf`, `PstarOf`, `Pstar N c3`, `PstarNat N c3`, `specPstar c3`, `PstarNatOf_eq` (P_* = value[X_1..X_5, X_0; 6]²) | proved (`c₃` a parameter) |

## Statement corrections and differences

1. **Fixed-scalar semantics.** The templates are parametric in the integer value `n = val(e)`
   (as in Templates/Multiply.lean), so the theorem is stated for `scalarTemplate I n` with
   `1 ≤ n`, under the hypothesis `I.psi = psiComponent` (the psi constructor read as the
   component polynomials), for `P ∈ carrierD` (= 2E(K₀)) and parameters `Fin.append (pointCode P) r`.
   No `DivisionPolynomialMultiplication` hypothesis is needed (`mulByN_formulas` is proved).
2. **Translation, constant table.** Instead of growing a global constant table, `translate`
   takes the table as an argument and maps a nontrivial constant `c` to template
   `18 + consts.idxOf c`: `power_value` uses `[4, 2, 3]`, `precision` uses
   `integerConstants c₃ = [4, 2, 3, c₃, 1399]`. This is the article's translation whenever the
   table lists the constants in order of first occurrence (for the power template this is the
   kernel check `powerTemplateCircuit_translationStats`: nontrivial constants `[4, 2, 3]`).
3. **Translation, ill-formed input is read totally** (the article leaves it undefined): an
   input-kind variable of index `≥ k` is treated as a witness variable; a `var` node without
   explicit variable and a reference to a later node get reference `-4` (five zeros); a
   constant missing from the table gets template index `18 + consts.length` (an empty template
   beyond the library). This makes `translate_inRange` (variables below the count) hold for
   every circuit. Identical to the article on well-formed circuits.
4. **Outer recipes.** The witness count of the callee recipe is a parameter of each
   composition recipe; `specRecipes` instantiates it with the witness count of the previous
   recipe. The call starts are those of the article exactly when the precision count is exact.
5. **Witness accounting** is stated as upper bounds, as instructed: `integers` has
   `739069 + w_prec` variables (exact, `specIntegers_variableCount_eq`) and `w_prec ≤
   292889492836`, so at most `292890231905` variables. The disjointness of private blocks is
   not proved here (not needed for the variable bound; nat-translation proves it for
   `translate`, the assembly chapter needs it for the composition recipes).
6. **Precision recipe.** The count needs only `PrecisionShape N c₃` (5 inputs, ≤ 54056
   explicit variables of which ≥ 5 are inputs, ≤ 125327 additions, ≤ 98382 multiplications,
   ≤ 15845 calls, nontrivial constants among `c₃, 2, 4, 1399`). `precisionShape_of` proves it
   for `precisionCircuitOf code` from nat-halting's counts and node statistics, the latter
   under nat-halting's named finite check `HaltingNodeCheck`. No property of `c₃` is needed
   (distinctness of `c₃` from `2, 4, 1399` matters only for exact counts).
7. **Zero projection.** `Rel_value(M, q)` is written
   `(valueExPoly ..).Rel (fun i => Fin.append M ![q] (Fin.cast (valueExPoly_params ..) i))`
   since the parameter count of the denotation is only propositionally `6`.

## Lemmas added beyond the leaves

- Scope.lean: `RefOK`, `varsLT_pointRef`, `ModelRecipe.InRange`, `ModelRecipe.varsLT_poly`,
  `ModelRecipe.denote_wf`, `CompositionRecipe.InRange`, `CompositionRecipe.varsLT_poly`,
  `CompositionRecipe.denote_wf`, `Recipe.denote_wf`, the fold invariant `TrInv`
  (`trVar_inv`, `trNode_inv`, `trState_inv`, `trVar_eq`), `translate_inRange`.
- Translate.lean: `foldl_trVar_next`, `foldl_trNode` (counter and distinct-constant bookkeeping),
  `varCost`, `nodeCost`, `nontrivialConst`.
- Precision.lean: `sum_varCost_true`, `sum_nodeCost`, `NatNode.isAdd`, `NatNode.isMul`,
  `PrecisionShape`.
- Accounting.lean: `Recipe.witnessCount`, `getEx_denoteRecipes_take`, `getEx_specLib`,
  `templateLibrary_getEx_wf`, `templateLibrary_getEx_witnesses`, the `*_inRange` lemmas of the
  five composition recipes, `specLib_wf_0 … specLib_wf_6`.
- FixedScalar.lean: `val_psiPair`, `holds_scalarFormula`, `zsmul_ne_zero_of_mem_carrierD`.
- Polynomial.lean / Literal.lean: `specConstructors` (fixedVal, psiComponent, guardPoly),
  `integers_rel_iff`, `exists_zero_integers_iff`, `exists_zero_PstarOf_iff`,
  `precisionShape_of`, `countKind_add`, `countKind_mul`.

## Finite computations

- `powerTemplateCircuit_translationStats` (`decide +kernel` on the 474 nodes, ~1 min).
- `witness_count_arith`, `variable_count_arith` (`decide`).
- Uses nat-halting's `HaltingNodeCheck` (a named finite check of milestone 1) via
  `precisionShape_of`. No new named check.

## Problems

None blocking. Pitfall met: the kernel recurses deeply when a goal like
`s + 5 + 140604 = s + 140609` (free `s`) is closed by definitional unfolding (e.g. by `simp`
closing with `rfl`, or `rfl` lemmas whose statement contains a recipe's witness count). Rewrite
with `Nat.add_assoc` or prove instance lemmas by applying the generic lemma (`exact
closeRecipe_variableCount _`) instead of `rfl`.

## Suggestions for the next agent

- When nat-programs provides the wrapper code `c₃`, instantiate `specPstar c₃`; FrozenTarget's
  witness is `specPstar c₃` with `specPstar_zero_projection` (third conjunct, together with the
  assembly chapter's `∃ M, Rel_value(M, q) ↔ q ∈ ℤ`) and `specPstar_spec` (coefficients and
  degree, for the size chapter's bounds on `PstarNat`).
- Exact counts (power_value is exact; precision `= 292889492861`) follow from
  `translate_variableCount` with the exact shape: needs the number of input-kind entries among
  the explicit variables to be exactly 5 and `c₃ ∉ {2, 4, 1399}` (from `1399 < c₃`).
- The relation of the outer recipes (assembly chapter) needs block disjointness for the
  composition recipes; `closeRecipe_calls`/`*_fresh` give the explicit starts for that.
