# Report: bp-audit-syntax

Task: audit the blueprint articles with `statement: formalized` under `syntax/` and
`compiler/translation/` (67 articles) against the Lean declarations in their `lean:` fields, and
fix drift in the article prose. Full findings: `docs/kernel-audits/blueprint-audit-2026-11-07-syntax.md`.
No Lean file was edited. `lake build ZInQKernel` succeeds; its only `sorry` is `Main.lean:34`,
as before. `autoform check blueprint --lean-root .` passes: 353 articles, 1201 dependencies,
897 names resolved.

## Summary

- **No article states something false about the Lean**, and every `lean:` name exists. All 200
  distinct names elaborate (`#check @name` over `import ZInQKernel`).
- **Four drifts, fixed in the article prose:**
  1. `syntax/recipes/recipe-precision.md`: the article gave exact counts (292,889,492,836
     witnesses, 292,889,492,861 variables). Lean proves only `≤ 292889492861` variables, under
     `PrecisionShape`. The statement now gives these bounds and spells out the shape.
  2. `syntax/recipes/fin-variable-form.md`: the "Moreover" paragraph compared $P_*$ with itself.
     It now says what `PstarOf_spec` states: `rename Fin.val P_* = [[integers]]`, degree and
     coefficients compared with `[[integers]]`, and the evaluation identity.
  3. `compiler/translation/translation-completeness.md`: "arbitrary values elsewhere" became
     "$0$ elsewhere". `translate_complete` is about one specific assignment, `TranslationShape.witness`.
  4. `syntax/templates/pole-semantics.md` (proof sketch): "node encoding $B\,S+(-1)\cdot0$"
     became "compilation $B\,S-0$". Templates have no node encoding in Lean.
- **Consistency rewordings:**
  - `syntax/recipes/outer-recipes.md`, last paragraph: the precision count is a bound.
  - `syntax/recipes/witness-accounting.md`: "$P_*$, which is $[\![\mathtt{integers}]\!]$ read in
    these variables".
- **An unexpected extra Lean hypothesis (reported, not changed).** `Translation.translate_rel_iff`
  (`compiler/translation/model-recipe-relation.md`) takes `PowerSetup`, whose field `spec` is (PV).
  The article does not assume (PV) and the proof does not use it. The article's statement is
  `modelRecipe_rel_iff` composed with `translate_scopedIn`.
- **Expected extra hypotheses** (`HaltingNodeCheck` / `PrecisionShape`):
  - fin-variable-form, witness-accounting, recipe-precision;
  - the parenthetical "no such variable occurs" of literal-polynomial.

  These are already recorded in final-audit F1, F4 and F5.
- **Harmless interpretation hypotheses.** Several theorems are generic in the constructor
  record `I`, with `hI : I.psi = psiComponent` or `hI : I.guard T = guardPoly T`.
  `specConstructors` satisfies both by `rfl`. This also settles the earlier remark that no
  record with `psiComponent` existed.
- **Lean stronger than the article.** `translate_sound` and `translate_complete` hold for any
  recipe with the shape of a translation (`TranslationShape`) and any callees with the needed
  semantics (`CalleeSemantics`). M implies the latter for the library (`calleeSemantics_library`).
- **Previous audit.** Of the 15 in-scope articles audited on 2026-11-06, only
  absolute-value-gadget changed: its WRONG verdict was fixed in `7692dc6`, and it is now
  faithful. The other 14 verdicts stand.

## Articles

Status is taken from the frontmatter: "proved" means `proof: formalized`, "definition" means a
definition article. Verdicts are relative to the Lean.

| Article path | Lean name | Status | Verdict |
| --- | --- | --- | --- |
| compiler/translation/lagrange-four-squares.md | `Translation.four_squares` | proved | faithful |
| compiler/translation/model-evaluation-semantics.md | `Translation.translate_rel_iff_zero`, `Translation.translate_rel_iff_value` | proved | faithful |
| compiler/translation/model-recipe-relation.md | `Translation.translate_rel_iff`, `Translation.modelRecipe_rel_iff` | proved | extra Lean hypothesis (unused (PV) in `translate_rel_iff`); statement proved via `modelRecipe_rel_iff` ∘ `translate_scopedIn` — reported, not changed |
| compiler/translation/natural-circuit-values.md | `Translation.nodeVal`, `Translation.circuitValue`, `Translation.templateValue`, … | definition | faithful |
| compiler/translation/natural-circuit-well-formed.md | `Translation.WellFormedCore`, `Translation.WellFormed` | definition | faithful |
| compiler/translation/natural-code-semantics.md | `Translation.MultiplicationExact`, `Translation.natural_rel_iff` | proved | faithful |
| compiler/translation/power-value-semantics.md | `Translation.powerValue_rel_iff`, `Translation.powerValue_spec` | proved | faithful |
| compiler/translation/precision-circuit-scope.md | `Translation.precisionCircuit_wellFormed`, `Translation.powerTemplate_wellFormed` | proved | faithful |
| compiler/translation/rational-translation.md | `Translation.precision_rel_iff`, `Translation.precision_rel_iff_accepts_of` | proved | faithful |
| compiler/translation/translation-completeness.md | `Translation.translate_complete` | proved | drift fixed ("arbitrary values elsewhere" → "$0$ elsewhere"); Lean more general |
| compiler/translation/translation-soundness.md | `Translation.translate_sound` | proved | faithful; Lean more general |
| syntax/constants/fixed-constants.md | `Syntax.Ps`, `Syntax.W`, `Syntax.Hcat`, … | definition | faithful |
| syntax/constants/fixed-integer-expressions.md | `Syntax.FixedExpr`, `Syntax.FixedExpr.val` | definition | faithful |
| syntax/constants/guard-product.md | `Syntax.guardPoly`, `Syntax.guardPoly_eval_eq_zero_iff` | definition | faithful |
| syntax/constants/least-formal-multiple.md | `Syntax.normalizedRep`, `Syntax.xi`, `Syntax.FormalCondition`, … | definition | faithful |
| syntax/constants/prime-catalogue.md | `Syntax.cataloguePrime`, `Syntax.catalogueProduct`, `Syntax.catalogueMax` | definition | faithful |
| syntax/constants/primorial-literal.md | `Syntax.primorial_324_eq`, `Syntax.four_mul_primorial_324_eq` | proved | faithful |
| syntax/division-polynomial-multiplication.md | `DivisionPolynomialMultiplication` | definition | faithful |
| syntax/division-polynomials-classical.md | `Syntax.normDiv_eq_preΨ'`, `Syntax.divPsi_eq_Ψ`, `Syntax.mk_divPsi`, … | proved | faithful |
| syntax/division-polynomials.md | `Syntax.normDiv`, `Syntax.divPsi`, `Syntax.psiComponent` | definition | faithful |
| syntax/field-pair-arithmetic.md | `Syntax.Pair.val`, `Syntax.holds_feq`, `Syntax.holds_curve` | proved | harmless difference (previous audit) |
| syntax/fixed-scalar-semantics.md | `Syntax.scalarTemplate_rel_iff_pointCode`, `Syntax.scalarTemplate_rel_iff_iota` | proved | faithful |
| syntax/language/absolute-value-gadget.md | `Syntax.eq_abs_iff_four_squares`, `Syntax.absTemplate_rel_iff` | proved | faithful (previous WRONG fixed, re-checked) |
| syntax/language/builder-soundness.md | `Syntax.Build.Allocates`, `Syntax.Build.Allocates.bind`, `Syntax.Build.template_construction` | proved | faithful |
| syntax/language/builder-well-formed.md | `Syntax.Formula.InScope`, `Syntax.ExPoly.WitnessScope`, `Syntax.ExPoly.WitnessScope.rel_iff`, … | proved | faithful |
| syntax/language/call-semantics.md | `Syntax.ev_callPoly`, `Syntax.ExPoly.exists_blockUpdate_call_iff` | proved | faithful |
| syntax/language/existential-lifting.md | `Syntax.Formula.exists_blocks_iff` | proved | faithful |
| syntax/language/field-pair-gadgets.md | `Syntax.Pair`, `Syntax.Build.fdiv`, `Syntax.Build.zGadget` | definition | faithful |
| syntax/language/formula-compilation.md | `Syntax.Formula`, `Syntax.Formula.compile`, `Syntax.Formula.Holds`, … | definition | faithful |
| syntax/language/generator-references.md | `Syntax.pointRef_eval_generator`, `Syntax.generatorConstraints_eq_zero_iff` | proved | harmless difference (previous audit) |
| syntax/language/point-references.md | `Syntax.pointRef`, `Syntax.generatorConstraints` | definition | faithful |
| syntax/language/positivity-gadget.md | `Syntax.pos_iff_four_squares`, `Syntax.exists_blockUpdate_posFormula_iff` | proved | faithful |
| syntax/language/rational-constants.md | `Syntax.ev_globals_eq_zero_iff`, `Syntax.generator_values` | proved | faithful |
| syntax/literal-polynomial.md | `Syntax.PstarNatOf`, `Syntax.PstarOf`, `Syntax.Pstar`, … | definition | faithful (parenthetical needs expected `PrecisionShape`) |
| syntax/nonzero-gadgets.md | `Syntax.exists_mul_eq_one_iff`, `Syntax.exists_mul_pairNorm_eq_one_iff` | proved | faithful |
| syntax/recipes/fin-variable-form.md | `Syntax.PstarOf_spec`, `Syntax.PstarOf_zero_projection`, `Syntax.specPstar_spec`, … | proved | drift fixed ("Moreover" paragraph now against $[\![\mathtt{integers}]\!]$); expected `HaltingNodeCheck` |
| syntax/recipes/model-evaluation-translation.md | `Syntax.translate`, `Syntax.translate_variableCount` | definition | faithful |
| syntax/recipes/outer-recipes.md | `Syntax.closeRecipe`, `Syntax.mainRecipe`, `Syntax.valueUnionRecipe`, … | definition | faithful; last paragraph reworded (precision count is a bound) |
| syntax/recipes/recipe-power-value.md | `Syntax.powerValueRecipe`, `Syntax.powerValueRecipe_variableCount` | definition | faithful |
| syntax/recipes/recipe-precision.md | `Syntax.precisionRecipe`, `Syntax.precisionRecipe_variableCount_le` | definition | drift fixed (exact counts → bounds under the circuit shape); expected `PrecisionShape` |
| syntax/recipes/template-witness-counts.md | `Syntax.templateLibrary_params`, `Syntax.templateLibrary_witnesses` | proved | faithful |
| syntax/recipes/witness-accounting.md | `Syntax.specRecipes`, `Syntax.specLib`, `Syntax.specLib_wf`, … | proved | faithful modulo expected `PrecisionShape`; one phrase reworded |
| syntax/recipes/witness-count-identity.md | `Syntax.witness_count_arith`, `Syntax.variable_count_arith` | proved | faithful |
| syntax/sum-of-squares-semantics.md | `Syntax.Formula.ev_compile_eq_zero_iff`, `Syntax.ev_sum_sq_eq_zero_iff`, `Syntax.ev_prod_eq_zero_iff` | proved | faithful |
| syntax/template-member.md | `Syntax.memberTemplate`, `Syntax.memberTemplate_rel_iff` | definition | faithful |
| syntax/template-raw-add.md | `Syntax.rawAddTemplate`, `Syntax.rawAddTemplate_rel_iff` | definition | faithful |
| syntax/template-semantics.md | `Syntax.Template.denote`, `Syntax.Recipe.denote`, `Syntax.ExPoly.Rel` | definition | harmless difference (previous audit) |
| syntax/templates/guard-semantics.md | `Syntax.guardTemplate_rel_codes3_iff`, `Syntax.guardTemplate_rel_iff_not_falseTriple_guardPoly` | proved | faithful |
| syntax/templates/log25-coefficients.md | `Syntax.log25Coeffs_spec` | proved | faithful |
| syntax/templates/pole-semantics.md | `Syntax.poleTemplate_rel_iff` | proved | faithful; proof-sketch drift fixed (node encoding → compiled atom) |
| syntax/templates/template-abs.md | `Syntax.absTemplate`, `Syntax.absTemplate_rel_iff` | definition | faithful |
| syntax/templates/template-close-coordinates.md | `Syntax.closeTemplate`, `Syntax.close_facts` | definition | faithful |
| syntax/templates/template-exceptions.md | `Syntax.exceptionsTemplate`, `Syntax.exceptions_facts` | definition | faithful |
| syntax/templates/template-fixed-scalar.md | `Syntax.scalarTemplate`, `Syntax.scalarTemplate_rel_iff` | definition | faithful |
| syntax/templates/template-guard.md | `Syntax.guardTemplate`, `Syntax.guardTemplate_rel_iff` | definition | faithful |
| syntax/templates/template-height-certificate.md | `Syntax.heightTemplate`, `Syntax.heightBuild_formula` | definition | faithful |
| syntax/templates/template-library.md | `Syntax.templateLibrary`, `Syntax.templateLibrary_witnesses`, `Syntax.templateLibrary_wf` | definition | faithful |
| syntax/templates/template-log25.md | `Syntax.log25Template`, `Syntax.log25Template_rel_iff` | definition | faithful |
| syntax/templates/template-multiply.md | `Syntax.multiplyTemplate`, `Syntax.multiplyBuild_formula` | definition | faithful |
| syntax/templates/template-natural.md | `Syntax.naturalTemplate`, `Syntax.naturalBuild_formula` | definition | faithful |
| syntax/templates/template-pole.md | `Syntax.poleTemplate`, `Syntax.poleTemplate_poly` | definition | faithful |
| syntax/templates/template-raw-inverse-x.md | `Syntax.rawInverseXTemplate`, `Syntax.rawInverseXTemplate_rel_iff` | definition | faithful |
| syntax/templates/template-raw-z.md | `Syntax.rawZTemplate`, `Syntax.rawZTemplate_rel_iff` | definition | faithful |
| syntax/templates/template-signed-encode.md | `Syntax.signedEncodeTemplate`, `Syntax.signedEncode_facts` | definition | faithful |
| syntax/templates/template-slope.md | `Syntax.slopeTemplate`, `Syntax.slopeBuild_formula` | definition | faithful |
| syntax/templates/template-test-group.md | `Syntax.testGroupTemplate`, `Syntax.testGroupBuild_formula` | definition | faithful |
| syntax/templates/template-value-test.md | `Syntax.valueTestTemplate`, `Syntax.valueTest_facts` | definition | faithful |

## Statement corrections

The four drifts and two rewordings above. No frontmatter, article id, dependency section or
other file under `blueprint/` was changed.

## Lemmas added beyond the leaves

None. This was an audit; no Lean was written.

## Problems

- `translate_rel_iff` carries an unused (PV) hypothesis (remark R1 of the audit document).
- The exact count of the precision recipe is not stated in Lean (R2). It is derivable under
  `HaltingNodeCheck` from `precisionCircuit_nodeStats` and `translate_variableCount`, but no
  consumer needs it.

## Suggestions for the next agent

- Add a (PV)-free variant of `translate_rel_iff` (taking only `PowerSetup.wf` and `.witnesses`)
  to the `lean:` field of model-recipe-relation, or add `ZInQ.Translation.translate_scopedIn`
  there.
- The audit document lists unlisted declarations for 12 articles (remark R3); the lead may add
  them to the `lean:` fields.
- `syntax/division-polynomial-multiplication.md` ends with a stale sentence ("its formal proof is
  a substantial project"); `ZInQ.mulByN_formulas` proves the proposition (R4).
- The docstring of `Compiler/Translation/WellFormed.lean` cites `nodeVal_congr`, but the lemma is
  `nodeVals_congr` (R5).
