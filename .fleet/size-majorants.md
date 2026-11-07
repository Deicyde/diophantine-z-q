# size-majorants: report

Height majorant, closure rules, template and recipe heights, admissible cutoff, and the final
degree and coefficient bounds (blueprint `size/majorants/`, `size/syntax-bounds.md`).
Directory `ZInQKernel/Size/Majorants/`, root module `ZInQKernel/Size/Majorants.lean` (imported
from `ZInQKernel.lean`), namespace `ZInQ.Size`. Branches `wip/size-norms`, `wip/size-constants`
(with `wip/size-formal`) and `wip/syntax-recipes` are merged. `lake build ZInQKernel` succeeds.
No `sorry`, `axiom` or `native_decide`; `#print axioms` gives `propext, Classical.choice,
Quot.sound` for every leaf theorem.

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| size/majorants/syntax-height.md | `Maj` (Basic.lean); `nodeHeight`, `nodeHeights`, `templateHeight`, `libraryHeights`, `modelCalleeHeights`, `callTargetHeight`, `recipeHeight`, `recipeHeights` (Height.lean) | proved (definitions) |
| size/majorants/majorant-rules.md | `Maj.mono`, `Maj.X`, `Maj.C`, `Maj.zero`, `Maj.add`, `Maj.mul`, `Maj.bind₁`, `Maj.constructor`, `Maj.rename`, `Maj.bind₁_of_maj_zero`, `Maj.sum_sq`, `Maj.prod` (Rules.lean) | proved |
| size/majorants/template-heights.md | `templateHeightTable`, `templateLibrary_maj` (TemplateHeights.lean); `templateLeanHeights`, `templateLibrary_maj_lean`; one majorant per template, `memberTemplate_maj` … `exceptionsTemplate_maj` (Templates.lean) | proved (restated, see 3) |
| size/majorants/node-majorant.md | `ConstructorBounds`, `NodeAdmissible`, `nodes_majorant`, `library_majorant`, `library_nodes_majorant` (NodeMajorant.lean); for the constructed library `LibraryAdmissible`, `templateLibrary_maj` | proved |
| size/majorants/recipe-heights.md | `recipe_heights` (`powerValue_maj`, `precision_maj`, `close_maj`, `main_maj`, `valueUnion_maj`, `value_maj`, `integers_maj`) (RecipeHeights.lean) | proved |
| size/majorants/recipe-majorant.md | `model_majorant`, `composition_majorant` (RecipeMajorant.lean) | proved |
| size/majorants/tower-comparison.md | `tower_bounds`, `degree_lt_tower_seven`, `coefficient_lt_tower_eight` (Towers.lean) | proved |
| size/majorants/admissible-cutoff.md | `admissible_cutoff`, `two_pow_sixtynine_lt_T`, `one_le_ell_value`, `D_le_T` (Cutoff.lean) | proved (hypothesis on `c₃`, see 7) |
| size/majorants/degree-coefficient-bound.md | `Pstar_degree_coeff`, `PstarNat_maj` (Bound.lean) | proved (hypotheses, see 8) |
| size/syntax-bounds.md | `Pstar_size`, `Pstar_target_bounds` (Bound.lean) | proved (hypotheses, see 8) |

## Statement corrections and differences

1. **Syntax heights.** The heights are defined, as in the article, on the node-list syntax of
   `ZInQKernel/Syntax/Language/Nodes.lean` (`Node`, `Template`, `Recipe`); references to missing
   nodes, templates or recipes get height `0`, matching their denotation `0`. `Maj` is generic
   in the variable type. The templates of the Lean library are `Build` programs, which have no
   node lists, so their intrinsic heights are not defined: for them the heights are replaced by
   majorant statements (item 3).
2. **Closure rules.** As stated, with two precisions. Rule 2 needs the hypothesis only for the
   variables of `P`. Rule 4 is also proved in the stronger form `Maj.bind₁_of_maj_zero`:
   substituting polynomials of degree and norm at most `1` (variables, `0`) keeps the height.
   Composition calls need this form, because `getPoly` reads a missing argument as `0`, so a
   composition call is a substitution by variables and `0` rather than a renaming. Rules 5 and 6
   do not need `1 ≤ m`.
3. **Template heights.** Restated for the `Build` library. Under `LibraryAdmissible B I c_* ℓ T c₃`
   (`B ≥ 2^20`, the uniform constructor bounds `ConstructorBounds I B`, `|n| + 1 ≤ B` for the psi
   indices, `|ℓ| ≤ B - 1`, `0 ≤ T ≤ B - 1`), every template `i < 23` satisfies
   `Maj B (templateHeightTable[i])`. The proofs give much smaller heights
   (`templateLeanHeights`: 1 for the templates without calls, `test_group` 2, `slope` 3,
   `height_certificate` 4, `S_ε` and the guard 2, `multiply` 6, `natural` 7, `signed_encode` 8,
   `value.test` 7, `close` and `exceptions` 2). The tabulated heights follow by monotonicity.
   Items 2 and 3 of the article (173 constant nodes below `2^69`, 50 constructor nodes) count
   node-list nodes and have no counterpart. In Lean the size calculus checks each literal
   constant by `decide` (all are below `2^128`), so constants need no hypothesis. The
   constructor occurrences are given by the construction: psi nodes occur only in `S_ε` with
   indices `ε, ε + 1, ε + (-1), 2ε`, `ε ∈ {c_*, 4, 2, 3, c₃, 1399}` (`psiIndices`), the guard at
   `T`, and `ℓ` only in `multiply`. These are exactly the fields of `LibraryAdmissible`.
4. **Node majorant.** Proved as stated for node-list libraries. The uniform constructor bounds,
   which the proof sketch takes from the norms chapter, are an explicit hypothesis
   (`ConstructorBounds`), since the theorem is generic in the constructors. For the
   specification's constructors this hypothesis is `specConstructors_bounds` (from size-norms'
   `psi_uniform`, `guard_uniform`).
5. **Recipe majorant.** (1) The hypothesis `h_κ ≥ 1` is not needed. The statement uses the
   computed callee heights: one hypothesis per kind of callee (natural template, constant
   definitions, operations), and at most `B` conjuncts. The point-reference arguments have
   height `1`, not `2`, so a model call costs `h_κ + 2 ≤ h_κ + 3`. (2) See item 2 for why the
   composition calls are substitutions rather than renamings.
6. **Recipe heights.** Stated for every precision circuit `N` with `PrecisionShape N c₃`
   (syntax-recipes), with generic constructors and constants under `LibraryAdmissible`. The
   constraint counts are proved from the translation without evaluating it: `power_value` has
   exactly `476` conjuncts (`powerValueRecipe_conjuncts_length`, from the kernel statistics of
   the power template) and `precision` has at most `293622` (`precisionRecipe_conjuncts_length_le`).
7. **Admissible cutoff.** `c₃` is a parameter of `specPstar` (the compiler chapter builds the
   wrapper code), so its size `|c₃| < 2^(2^24)` is a hypothesis. It follows from
   `Compiler.Universal.code_lt_of_small` and `two_pow_14400019_lt` once the wrapper program is
   fixed. Item 1 is stated as `2^69 < T`. All psi indices are bounded through
   `|n| + 1 ≤ 2^(2^2060) < D ≤ T`. `D ≤ T` (`D_le_T`) follows from the chain
   `D ≤ R ≤ Q ≤ 2·10^13 Q^17 ≤ A_ht ≤ T`.
8. **Degree/coefficient bounds and syntax-bounds.** Besides the catalogue bound, both take the
   inputs that the specified polynomial depends on: `HaltingNodeCheck`, the compiler chapter's
   named finite check, and `|c₃| < 2^(2^24)`. `HaltingNodeCheck` enters through syntax-recipes'
   `precisionShape_of`, which the Fin form `specPstar_spec` needs and which gives the precision
   conjunct count. `Pstar_degree_coeff` also bounds `‖P_*‖₁ ≤ 2^((T+1)^2048)`.
   `Pstar_target_bounds` is exactly the first two conjuncts of `FrozenTarget` for
   `specPstar c₃`. The variable count is the type `Fin 292890231905`.

## Lemmas added beyond the leaves

- **The finer scale** (Basic.lean, Calculus.lean). `Scale B e s P` means `deg P ≤ 2^s B^e` and
  `‖P‖₁ ≤ 2^(2^s B^e)`. A ring operation raises `s` by one, a substitution adds the exponents,
  and `2^s ≤ B^d` trades `s` for `d` more powers of `B` (`Scale.lift`). Since `B ≥ 2^20`, up to
  160 operations cost one height level. The scale is extended to pairs (`PScale`), argument
  tuples and codes (`AScale`) and lists of formulas (`FAll`), with max-style rules (`Scale.add'`,
  `PScale.mul'`, `Scale.call'`, `Scale.compile_and'`, …). Three loops get rules proved by
  induction: repeated squaring (`PScale.powAux`, `PScale.pow`), `slopeW` (`PScale.slopeW'`) and
  `log25` (`PScale.log25'`). `maj_of_sz` turns a scale bound into a majorant.
- **The tactic `size`** (Tactic.lean), with `size_maj` (proves `Maj B (h+1) P`) and `size_le`
  (proves `Scale B e s P`). It applies the rules from the root of the explicit formula to the
  leaves, reads callee and constructor bounds from hypotheses, and closes numeric side
  conditions by `Nat.ble` evaluation, `decide` or `simp`. It never unfolds a template polynomial.
- **Exceptional values**: `sz_rational`, `asz_gen`, `chainBuild_sz` (the double-and-add chain,
  by induction), `exceptionBranch_sz`, `length_binDigits`.
- **Translation counts**: `length_conjuncts`, `foldl_trVar_counts`, `trNode_counts`,
  `foldl_trNode_counts`, `opCount`, `sum_opCount`, `translate_conjuncts_length`,
  `translate_constants_ge`, `sum_varCost_false`, `translate_majorant`,
  `recipeHeight_translate_le`, `specLib_composition_maj`, `callTarget_maj`,
  `templateLibrary_maj_all`.
- **Constants**: `D_le_T`, `two_pow_two_pow_lt_T`, `two_pow_twenty_le_T_add_one`,
  `specConstructors_bounds`, `guard_cond_of`, `fixed_cond_of`, `two_mul_two_pow_two_pow_le`.

## Problems

- **Name clashes after merging.** size-norms also defines `ZInQ.Size.Sz` and `l1_rename_le`, and
  size-constants defines `ZInQ.Size.triplePower_eq`. I renamed my scale to `Scale`, reused
  size-norms' `l1_rename_le` and renamed my tower lemmas to `triplePower_eq_pow` and
  `quadruplePower_eq_pow`. Commit `96442bf` (the merge) does not build; `c58246d` fixes it.
- **Evaluation of the big constants.** I hit three traps beyond those listed in the task:
  - `rw` ends with a `rfl` attempt, which on a goal such as `ℓ + 1 ≤ T + 1` evaluates
    `T + 1` (a deterministic timeout, or the kernel refusing to evaluate `Nat.pow`).
  - `generalize 2 ^ 2 ^ 2059 = X` followed by `omega` panics ("Nat.pow exponent is too big"):
    the definitional-equality checks of `kabstract` fold literal powers.
  - Comparing `0 ≤ (T : ℤ)` with a lemma through different instance paths makes the kernel
    unfold `T`.

  Remedies: use `rewrite` instead of `rw`, and prove small lemmas for variables
  (`guard_cond_of`, `fixed_cond_of`, `two_mul_add_two_le`) that are then instantiated at `T`.
- **Tactic pitfall.** A last `first` alternative run by `evalTactic` is in error-recovery mode,
  so `(simp; done)` logged its error and left the goal open ("declaration has metavariables").
  `sideGoal` now checks that the goal is closed and its proof has no metavariables or `sorry`.

## Suggestions for the next agent

- When the wrapper program and its code `c₃` are fixed (nat-programs), discharge
  `hc3 : c₃.natAbs < 2^(2^24)` with `code_lt_of_small` and `two_pow_14400019_lt`.
  `Pstar_target_bounds hCAT hH hc3` then gives the degree and coefficient conjuncts of
  `FrozenTarget` for `specPstar c₃`. The third conjunct comes from `specPstar_zero_projection`
  with the assembly chapter.
- `HaltingNodeCheck` is the only finite-computation input used here. When the compiler chapter
  replaces it by symbolic upper bounds, `PrecisionShape` is all that recipe heights and the
  witness accounting need.
- The blueprint's template-height table and node counts can be replaced by the Lean heights
  (`templateLeanHeights`, at most 8) and the hypothesis list `LibraryAdmissible`. With the Lean
  heights the root height would be far below 256, but the statements keep the tabulated
  heights and `(T+1)^2048`, as in the blueprint.
- `size` / `size_maj` can bound any explicit polynomial built from pairs, codes, gadgets and
  calls: put the callee and constructor bounds in the context as `Scale` hypotheses.
