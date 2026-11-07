# cleanup-2: report

Behaviour-preserving cleanup across `ZInQKernel/`. No blueprint-named declaration was renamed or
removed, and none had its statement changed. All nine commits were each preceded by a full
`lake build ZInQKernel` that succeeded. The only `sorry` in the build is the existing one in
`ZInQKernel/Main.lean` (`exists_bounded_integer_polynomial_defining_integers_of`), which I did not
touch because that file was out of scope.

## Items

| item | Lean names | status |
|---|---|---|
| 1. `exists_prime_dvd_natCast` | `ZInQ.Mult.exists_prime_dvd_natCast`, now in `Multiplication/Local/PrimesAbove.lean` | merged: the copies in `Mult` (Soundness/CommonGroup), `Assembly` (Local/TestDivisibility) and `Size` (FormalMultiple/OddCoefficients) are removed |
| 2. `Size/FormalMultiple/FormalMul.lean` | `Size.nsmul_mem_formalFilt_add`, `Size.nsmul_mem_formalFilt_of_val` (statements unchanged) | merged: `Size.formal_third_point_five`, `Size.chord_add_five`, `Size.zCoord_neg'`, `Size.zCoord_add_sub_ge` and `Size.zCoord_nsmul_sub_ge` are removed. They duplicated `Mult.formal_third_point_five`, `Mult.chord_add_five`, `Mult.zCoord_neg`, `Assembly.val_zCoord_add_sub` and `Assembly.val_zCoord_nsmul_sub`. The one-step lemma is now `Assembly.zsmul_mem_formalFilt_of_vge` applied at the level of the point. |
| 3. Outer recipe disjointness | `Syntax.CompositionRecipe.callBlocks`, `Syntax.{close,main,valueUnion,value,integers}Recipe_callBlocks_disjoint` | merged: moved from `Syntax/Builder/Recipes.lean` to `Syntax/Recipes/Outer.lean` (names unchanged). `Builder/Recipes` imports `Assembly/Values/Outer`, so importing it from Outer would have made a cycle. `close_rel_iff`, `main_rel_iff`, `valueUnion_rel_iff` and `value_rel_iff` now use these lemmas instead of the inline proofs. |
| 4. Duplicates | see below | script `scripts/find_duplicates.py`; clear cases merged, rest listed below |
| 5. Stale comments | module docs of `Model/DivisionPolynomials/FixedPointCodes`, `Assembly/Real/Accumulation`, `Multiplication/Certificate/Multiply`, `Assembly/Close/Relation` | fixed |
| 6. Deprecations | 175 occurrences | fixed: `if_pos/if_neg → ite_eq_left/ite_eq_right`, `dif_pos/dif_neg → dite_eq_left/dite_eq_right`, `if_true/if_false → ite_true/ite_false`, `cond_true/cond_false → Bool.cond_*`, `Set.mem_setOf_eq → Set.mem_ofPred_eq`, `push_neg → push Not`. The build log now has no deprecation warnings (174 warnings remain, all linter warnings: unused simp arguments and variables, `module` hints). |

## Item 4: what was merged (one copy kept)

`scripts/find_duplicates.py` scans the source text without running Lean. It lists theorem names
declared in more than one place or namespace, and theorems with the same (whitespace-normalised)
statement under different names. Run it with `python3 scripts/find_duplicates.py`.

- `ZInQ.toK0_ne_zero`: this full name was declared twice, in `Model/Descent/Factor` and
  `Model/Heights/CommonDivisor`; the build still accepted it. It now exists once, together with
  `ZInQ.toK0_star` (which had copies in `ZInQ` and `Compiler.Precision`), in
  `Model/Field/Basic.lean`.
- `ZInQ.genP0_not_isOfFinAddOrder`: the `Mult` copy is removed, and `Local/Nonvanishing` now
  imports `Model/Generator/InfiniteOrder`. `Mult.zsmul_genP0_ne_zero` replaces the `Assembly`
  copy.
- `Mult.zCoord_neg` is now stated in `Local/FormalGroup` without `[DecidableEq K]`. Removed:
  the copies in `Local/FormalLogarithm` and `Assembly/Local/FormalMultiplication`, and
  `Mult.zCoord_neg'` (FormalLog/ChordEval).
- `ZInQ.neg_genD_sq_eq_toK0` and `ZInQ.vge_neg_genD_sq` replace the copies in `Mult`
  (Completeness/SelectedReduction) and `Size` (FormalMultiple/BadPlace, including
  `Size.vge_genA`). `BadPlace` now imports `Model/Descent/OddTorsion`.
- `ZInQ.genD_sq` replaces `Mult.genD_sq_eq`, and `ZInQ.shortCurve_negY` replaces
  `Compiler.Precision.JTriple.shortCurve_negY'`.
- `ZInQ.Zs.norm_eq` and `ZInQ.Zs.norm_ne_zero` replace the `Compiler.Precision` copies, and
  `Precision/NormZero` now imports `Model/Field/Euclidean`.
- Mult/Assembly pairs:
  - `Mult.star_dvd_natCast`, `Mult.star_ratCast`, `Mult.vp_prod` and
    `Mult.padicValRat_intCast_eq_zero` are now in `Local/PrimesAbove`.
  - `Mult.vP_star` is now in `Local/Valuations`, which now imports PrimesAbove.
  - Removed: the copies in `Assembly/Local/TestDivisibility` (including
    `Assembly.prime_star_dvd`), `Soundness/CommonGroup`, `Soundness/TestsToCongruence`,
    `Completeness/PoleValuationsAux` and `Soundness/ContactValuations`.
- `Syntax.lift_feq`, `Syntax.lift_fin` and `Syntax.lift_nzFormula` (in `Syntax/Language`)
  replace the `Assembly` and `Mult` copies.
- The definition `contactPoly` existed twice with the same body, as `Assembly.contactPoly` and
  `Mult.contactPoly`:
  - The assembly copy and its `contactPoly_eq_prod` are removed.
  - `Assembly/Local/SixLocalTests` now imports `Multiplication/Certificate/Constants`.
  - `Assembly.testR₀`, `testC`, `vtR0` and so on now refer to `Mult.contactPoly`.
  - The blueprint-named def `ZInQ.Assembly.Test` keeps its text and its meaning.
- `Mult.poleSystem_of_polePoly_eq_zero` replaces `Assembly.poleSystem_of_polePoly`, and
  `ZInQ.zsmul_genP0_affine` replaces `Assembly.exists_zsmul_genP0_eq_some`.
- `Mult.codes3_iota`, `Mult.guardPoly_zero_set` and `Mult.guard_rel_iff` are blueprint-named,
  so they are kept, but each is now a one-line proof from `Cleanup/GuardSemantics` (same
  statements). `Mult/Certificate/Guard` imports that module.
- Proofs replaced by their twins: `Syntax.eq_pointCode_some_iff` now follows from
  `ZInQ.eq_pointCode_some_iff`, and `Size.totalDegree_bind₁_le` from
  `Syntax.totalDegree_bind₁_le`.
- Pure aliases removed: `Translation.templateLibrary_wf'`, `Size.Hmax_lt`,
  `Mult.two_mul_ten_pow_thirteen_le_Aht`, `ZInQ.divisionPolynomialMultiplication` (unused; the
  blueprint names `mulByN_formulas`), and `Compiler.Natural.nv_X'` (replaced by
  `attribute [simp] nv_X`).

## Item 4: what was left, and why

These are definitions or statements that are equal but not syntactically identical. Merging them
would change the statements of blueprint-named theorems, or needs a larger refactor.

- **Four definitions of `z = -x/y` on `E(K₀)`**: `Mult.zCoord` (general `A`),
  `Assembly.zCoord` (blueprint-named, `real-derivative`), `Compiler.Precision.zPt` and
  `Mult.zOf` (Certificate/Tests). The equalities are proved in `Cleanup/Bridges`.
  `Mult.invX` and `Syntax.xi` are likewise one definition, `w = 1/x`, written twice.
- **Two reachability notions and two wrappers on the same register machines**:
  `Compiler.Universal.Reaches` and `Compiler.IR.Reaches` are definitionally equal (both have
  `Reaches.refl`). Related pairs: `Universal.reaches_clear` / `IR.reaches_clear` and
  `stepN_eq_none_of_halt`. `Universal.wrapper` and `IR.wrapper` are different constructions of
  the halting wrapper, and both `wrapper_valid` and `wrapper_length` are blueprint-named.
- `Translation.powerCallee` = `Syntax.ModelRecipe.powerCallee`, and `Translation.Nontrivial` =
  `Syntax.IsNontrivial`. They have the same bodies but appear in the statements of the
  translation-chapter lemmas. `Compiler.Precision.degFn` = `Syntax.FixedFormula.D`.
- `Assembly.val_slopeW_foldl` vs `Mult.val_slopeW_foldl`: these differ only in
  `algebraMap ℚ K0` vs the coercion. Similar pairs: `evCode_varPoint` and `val_varPair` (`pt`
  and `pr` vs explicit terms), `shortCurve_map` (two forms), `abs_re_add_abs_im_le` (ℝ vs ℚ),
  `ev_norm_eq` (norm vs `re² - 2 im²`), and `Size.add_of_red_opp`, which refines
  `ZInQ.add_of_red_opp`.
- `ZInQ.VGe π` (Model/Descent/Residue) and `Mult.Vge v` (Local/ValHelpers) are two valuation
  predicates with parallel APIs: `mono`, `add`, `mul`, `vge_natCast`, `one_add_ne_zero`, and so
  on.
- Same short name with different content, which is harmless: `Assembly.Pstar_spec` vs
  `Syntax.Pstar_spec`; `ZInQ.cataloguePrime_spec` and `ZInQ.infinite_catalogue_class` (the
  instances) vs the general `Syntax.*`; `FixedFormula.*_eq` vs `Syntax.*_eq` (formula vs
  constant, by design). The many dot-notation families (`X.mono`, `X.add`, …) are also expected.

## Notes for the blueprint

- `closeRecipe_callBlocks_disjoint` through `integersRecipe_callBlocks_disjoint` and
  `CompositionRecipe.callBlocks` now live in `ZInQKernel/Syntax/Recipes/Outer.lean`. Their names
  are unchanged (article `syntax/language/builder-well-formed.md`).
- No blueprint file mentions a removed name (checked with grep over `blueprint/`).

## Problems

None blocking.

## Suggestions for the next agent

- Unify the four `z` definitions behind `Mult.zCoord (A := -genD ^ 2)`, and `Universal.Reaches`
  with `IR.Reaches`. The blueprint `lean:` fields of `real-derivative` and of the wrapper
  articles would then have to move with them.
- Remove the linter warnings: 19 unused simp arguments, 9 unused tactics, unused variables and
  section variables.
