# Blueprint audit of the syntax and translation articles (task bp-audit-syntax)

Scope: the 67 articles under `blueprint/roadmap/syntax/` and
`blueprint/roadmap/compiler/translation/` whose frontmatter has `statement: formalized`.
Audited at commit `de90139`.

For each article, the statement was compared with the Lean declarations in its `lean:` field. The
statement is the text before "**Proof sketch.**", or before the first `##` heading for definition
articles. The comparison covered hypotheses, quantifiers and their ranges, conclusions, constants
and the objects the statement is about. Proof-sketch prose was also checked where it describes
the Lean construction.

## Summary

- **No article states something false about the Lean**, and every `lean:` name exists. All 200
  distinct names elaborate in a scratch file importing `ZInQKernel` (`#check @name` for each).
- **Four drifts, fixed in the article prose:**
  1. `syntax/recipes/recipe-precision.md` claimed exact witness and variable counts. Lean proves
     only upper bounds, and only under the circuit shape `PrecisionShape`.
  2. `syntax/recipes/fin-variable-form.md` compared $P_*$ with itself. Lean compares $P_*$ with
     $[\![\mathtt{integers}]\!]$.
  3. `compiler/translation/translation-completeness.md` claimed the witness works with
     "arbitrary values elsewhere". Lean builds one assignment, with $0$ elsewhere.
  4. `syntax/templates/pole-semantics.md` (proof sketch) described a node encoding
     $B\,S+(-1)\cdot0$. The Lean template polynomial is the compiled formula $B\,S-0$, and no
     node encoding exists.
- **Two consistency rewordings** follow from item 1:
  - `syntax/recipes/outer-recipes.md` now treats the precision count as a bound.
  - `syntax/recipes/witness-accounting.md` now says "$P_*$, which is
    $[\![\mathtt{integers}]\!]$ read in these variables".
- **One extra Lean hypothesis is not expected:** `ZInQ.Translation.translate_rel_iff`
  (`compiler/translation/model-recipe-relation.md`) takes `PowerSetup`. One of its fields is
  (PV), which the article does not assume and the proof does not use. The article's statement is
  still proved, by `modelRecipe_rel_iff` composed with `translate_scopedIn`. See remark R1.
- **Expected extra hypotheses** (`HaltingNodeCheck`, or its consequence `PrecisionShape`):
  - `syntax/recipes/fin-variable-form.md`;
  - `syntax/recipes/witness-accounting.md`;
  - `syntax/recipes/recipe-precision.md`;
  - the parenthetical "no such variable occurs" of `syntax/literal-polynomial.md`.

  These are already recorded as F1, F4 and F5 of `final-audit-2026-11-07.md`.
- **Interpretation hypotheses (harmless).** The template and translation theorems are generic in
  the constructor record `I : Constructors E`. Some take `hI : I.psi = psiComponent`; the guard
  theorems take `hI : I.guard T = guardPoly T`. The specification's record `specConstructors`
  satisfies both by `rfl` (`specConstructors_psi`). This also settles the remark of
  `lean-audit-2026-11-06.md` that no constructor instance with `psiComponent` existed.
- **Lean stronger than the article** (fine):
  - Translation soundness and completeness are stated for any recipe with the shape of a
    translation (`TranslationShape`) and any callees with the needed semantics
    (`CalleeSemantics`). M implies the latter for the library (`calleeSemantics_library`).
  - The rational-translation theorem takes (C.4) as an explicit hypothesis, as the article says.

Articles re-checked from the previous audit: of the 15 in scope, only
`syntax/language/absolute-value-gadget.md` changed since `0bea4dc`. Its WRONG verdict was fixed
in `7692dc6` and the article is now faithful. The Lean of the other 14 changed only by docstrings
or added `Lift` lemmas (`git diff 0bea4dc HEAD -- ZInQKernel/Model/DivisionPolynomials ZInQKernel/Syntax/Language`).
Their earlier verdicts stand and are copied below.

`uv run --project ~/autoform-dzq autoform check blueprint --lean-root .` passes after the edits:
353 articles, 1201 dependencies, 897 names resolved.

## Verdicts

Lean names are in namespace `ZInQ`: `Translation.` is `ZInQ.Translation`, and unprefixed names in
the syntax rows are in `ZInQ.Syntax`.

### compiler/translation

| Article | Lean names | Verdict | Changed / to change |
| --- | --- | --- | --- |
| lagrange-four-squares | `Translation.four_squares` | faithful | — |
| model-evaluation-semantics | `translate_rel_iff_zero`, `translate_rel_iff_value` | faithful; Lean generic in `I` with `hI : I.psi = psiComponent`; `PowerSetup` packages "well-formed π with (PV) if call nodes" plus the bookkeeping that the recorded witness count is π's | — |
| model-recipe-relation | `translate_rel_iff`, `modelRecipe_rel_iff` | **extra Lean hypothesis** in `translate_rel_iff`: (PV), field `spec` of `PowerSetup`, unused; the article's (PV)-free statement is `modelRecipe_rel_iff` ∘ `translate_scopedIn`; the values `ι(0), ι(1), ι(−1)` of the references `−1, −2, −3` are `refVal_generator`, `refVal_negative`; "only the values at the parameters and free witnesses matter" is an informal remark | no text change; see R1 |
| natural-circuit-values | `nodeVal`, `circuitValue`, `templateValue`, `callValue`, `circuitPoly`, `Admissible`, `circuitValue_eq_eval_poly` | faithful (definition); the sentence on the precision circuit is `callTemplate_powerTemplate`, `circuitValue_precision`, `precisionCircuit_counts`, `powerTemplateCircuit_varCount` (unlisted) | — |
| natural-circuit-well-formed | `WellFormedCore`, `WellFormed` | faithful (definition); "decidable predicate" is not instantiated (a `Prop` structure, no `Decidable` instance), harmless; the locality remark is `nodeVals_congr`, `circuitValue_congr_lt`, `nodeVal_update_block` (unlisted) | — |
| natural-code-semantics | `MultiplicationExact`, `natural_rel_iff` | faithful (generic in `I`) | — |
| power-value-semantics | `powerValue_rel_iff`, `powerValue_spec` | faithful; `hI` | — |
| precision-circuit-scope | `precisionCircuit_wellFormed`, `powerTemplate_wellFormed` | faithful; no node-check hypothesis | — |
| rational-translation | `precision_rel_iff`, `precision_rel_iff_accepts_of` | faithful; `hI`; structural hypothesis `hrec` (recipe 0 of the recipe list is `power_value`); (C.4) is the explicit hypothesis `hC4`, as the article says (proved as `Compiler.natural_polynomial_semantics'`) | — |
| translation-completeness | `translate_complete` | **drift (fixed)**: article said "arbitrary values elsewhere", Lean's witness `TranslationShape.witness` is $0$ elsewhere. Lean more general (`TranslationShape`, `CalleeSemantics`). The closing "Consequently … Rel_ρ holds" is the ⇐ half of `TranslationShape.rel_iff_zero` / `rel_iff_value`, used by `translate_rel_iff_zero` / `_value` | "arbitrary values elsewhere" → "$0$ elsewhere" |
| translation-soundness | `translate_sound` | faithful; Lean more general (as above); `θ_i = c_i` follows from injectivity of `ι`; the "in particular" sentence is in `TranslationShape.rel_iff_zero` / `rel_iff_value` | — |

### syntax/constants

| Article | Lean names | Verdict | Changed / to change |
| --- | --- | --- | --- |
| fixed-constants | `Ps`, …, `T`, `integerConstants`, `Compiler.Universal.c3` | faithful (definition); "$A_{\rm ht}=H_6(S;R)$" is `Mult.Aht_eq_heightH6`, "$1399<c_3<2^{2^{24}}$" is `c3_gt`, `c3_lt'` (unlisted) | — |
| fixed-integer-expressions | `FixedExpr`, `FixedExpr.val` | faithful | — |
| guard-product | `guardPoly`, `guardPoly_eval_eq_zero_iff` | faithful | — |
| least-formal-multiple | `normalizedRep`, `xi`, `FormalCondition`, `leastFormalMultiple` | faithful; existence and uniqueness of the normalized representation are `normalizedRep_isNormalizedRep`, `IsNormalizedRep.eq_normalizedRep` (unlisted) | — |
| prime-catalogue | `cataloguePrime`, `catalogueProduct`, `catalogueMax` | faithful (`p % W = r` for `r < W`); Dirichlet is `infinite_catalogue_class` (unlisted) | — |
| primorial-literal | `primorial_324_eq`, `four_mul_primorial_324_eq` | faithful (literals compared character by character); "66 primes", "433 / 435 binary digits" are `card_primes_le_324`, `digits_two_primorial_324_length`, `digits_two_four_mul_primorial_324_length` (unlisted) | — |

### syntax (top level)

| Article | Lean names | Verdict | Changed / to change |
| --- | --- | --- | --- |
| division-polynomial-multiplication | `DivisionPolynomialMultiplication` | faithful (previous audit; unchanged); the last sentence ("its formal proof is a substantial project") is stale: `mulByN_formulas` proves it | — (see R4) |
| division-polynomials-classical | `normDiv_eq_preΨ'`, `divPsi_eq_Ψ`, `mk_divPsi`, `psiEval_eq_evalEval_ψ` | faithful (previous audit) | — |
| division-polynomials | `normDiv`, `divPsi`, `psiComponent` | faithful; the earlier "harmless difference" (no constructor record with `psiComponent`) is resolved by `specConstructors` | — |
| field-pair-arithmetic | `Pair.val`, `holds_feq`, `holds_curve` | harmless difference (previous audit: list incomplete) | — |
| fixed-scalar-semantics | `scalarTemplate_rel_iff_pointCode`, `scalarTemplate_rel_iff_iota` | faithful; `hI`; `P ∈ carrierD` is `P ∈ 2E(K₀)` | — |
| literal-polynomial | `PstarNatOf`, `PstarOf`, `Pstar`, `specPstar` | faithful (definition); the parenthetical "no such variable occurs" needs `PrecisionShape` (from `HaltingNodeCheck`), expected; "unfolding the root" is `PstarNatOf_eq` (unlisted) | — |
| nonzero-gadgets | `exists_mul_eq_one_iff`, `exists_mul_pairNorm_eq_one_iff` | faithful (previous audit) | — |
| sum-of-squares-semantics | `Formula.ev_compile_eq_zero_iff`, `ev_sum_sq_eq_zero_iff`, `ev_prod_eq_zero_iff` | faithful (previous audit) | — |
| template-member | `memberTemplate`, `memberTemplate_rel_iff` | faithful (definition; variables and formula checked) | — |
| template-raw-add | `rawAddTemplate`, `rawAddTemplate_rel_iff` | faithful (definition) | — |
| template-semantics | `Template.denote`, `Recipe.denote`, `ExPoly.Rel` | harmless difference (previous audit); the constructor record of the specification now exists (`specConstructors`) | — |

### syntax/language

| Article | Lean names | Verdict | Changed / to change |
| --- | --- | --- | --- |
| absolute-value-gadget | `eq_abs_iff_four_squares`, `absTemplate_rel_iff` | faithful (re-checked; WRONG of the previous audit fixed in `7692dc6`) | — |
| builder-soundness | `Build.Allocates`, `Build.Allocates.bind`, `Build.template_construction` | faithful; "every primitive is allocating" is `Build.Allocates.fresh`, `.call`, `.rational`, `.nz`, `.pos`, … (unlisted) | — |
| builder-well-formed | `Formula.InScope`, `ExPoly.WitnessScope`, …, `specLib_precisionCircuit_witnessScope` | faithful; `InScope` also requires `p ≤ v`, implicit in the article; bounds $B=51,11,6,6,6$ checked | — |
| call-semantics | `ev_callPoly`, `ExPoly.exists_blockUpdate_call_iff` | faithful (previous audit) | — |
| existential-lifting | `Formula.exists_blocks_iff` | faithful (previous audit) | — |
| field-pair-gadgets | `Pair`, `Build.fdiv`, `Build.zGadget` | faithful (previous audit) | — |
| formula-compilation | `Formula`, `Formula.compile`, …, `Build.pos` | faithful (definition) | — |
| generator-references | `pointRef_eval_generator`, `generatorConstraints_eq_zero_iff` | harmless difference (previous audit) | — |
| point-references | `pointRef`, `generatorConstraints` | faithful (previous audit) | — |
| positivity-gadget | `pos_iff_four_squares`, `exists_blockUpdate_posFormula_iff` | faithful (previous audit) | — |
| rational-constants | `ev_globals_eq_zero_iff`, `generator_values` | faithful (previous audit) | — |

### syntax/recipes

| Article | Lean names | Verdict | Changed / to change |
| --- | --- | --- | --- |
| fin-variable-form | `PstarOf_spec`, `PstarOf_zero_projection`, `specPstar_spec`, `specPstar_zero_projection` | **drift (fixed)**: the "Moreover" paragraph said "total degree at most that of $P_*$" and "$\mathrm{coeff}_d(Q)=\mathrm{coeff}_{\iota_*d}(P_*)$" with $Q$ itself $P_*$; Lean: `rename Fin.val P_* = [[integers]]`, degree and coefficients against `[[integers]]`, and the evaluation identity. Expected extra hypothesis `HaltingNodeCheck` / `PrecisionShape` | "Moreover" paragraph rewritten against $[\![\mathtt{integers}]\!]$, evaluation identity added |
| model-evaluation-translation | `translate`, `translate_variableCount` | faithful (definition); Lean is total on ill-formed input (documented in `Translate.lean`); the constant table form is the article's "equivalently" | — |
| outer-recipes | `closeRecipe`, …, `integersRecipe` | faithful (definition; starts and counts checked against `closeRecipe_calls`, … and `closeRecipe_variableCount = 703321 + w + 53`) | last paragraph: the precision count is the bound, displayed values are upper bounds |
| recipe-power-value | `powerValueRecipe`, `powerValueRecipe_variableCount` | faithful (exact count) | — |
| recipe-precision | `precisionRecipe`, `precisionRecipe_variableCount_le` | **drift (fixed)**: article gave exact counts $292{,}889{,}492{,}836$ / $292{,}889{,}492{,}861$; Lean proves `≤ 292889492861` variables under `PrecisionShape` (5 inputs first among ≤ 54056 explicit variables, ≤ 125327 / 98382 / 15845 add / mul / call nodes, constants among $c_3,2,4,1399$). No consumer needs the exact count | statement now gives the bounds under that shape |
| template-witness-counts | `templateLibrary_params`, `templateLibrary_witnesses` | faithful (both lists compared entry by entry; universally quantified over the constants) | — |
| witness-accounting | `specRecipes`, …, `vars_integers_lt` | faithful (already says "at most"); bounds need `PrecisionShape` (expected, final audit F4) | "$P_*=[\![\mathtt{integers}]\!]$" → "$P_*$, which is $[\![\mathtt{integers}]\!]$ read in these variables" |
| witness-count-identity | `witness_count_arith`, `variable_count_arith` | faithful (identities compared term by term) | — |

### syntax/templates

All template definitions were checked against the Lean `…Formula` / `…Blocks` / `…Globals`
terms: parameter positions, allocation order, block starts and lengths, rational constants,
formula order, and the `…_facts` counts.

| Article | Lean names | Verdict | Changed / to change |
| --- | --- | --- | --- |
| guard-semantics | `guardTemplate_rel_codes3_iff`, `guardTemplate_rel_iff_not_falseTriple_guardPoly` | faithful; `hI : I.guard T = guardPoly T` | — |
| log25-coefficients | `log25Coeffs_spec` | faithful | — |
| pole-semantics | `poleTemplate_rel_iff` | faithful; **proof-sketch drift (fixed)**: "node encoding $B\,S+(-1)\cdot0$" → "compilation $B\,S-0$" (`poleTemplate_poly`) | proof sketch |
| template-abs | `absTemplate`, `absTemplate_rel_iff` | faithful | — |
| template-close-coordinates | `closeTemplate`, `close_facts` | faithful | — |
| template-exceptions | `exceptionsTemplate`, `exceptions_facts` | faithful; chain lengths $0,7,6,6,8,9$ follow from `binDigits_contacts` | — |
| template-fixed-scalar | `scalarTemplate`, `scalarTemplate_rel_iff` | faithful | — |
| template-guard | `guardTemplate`, `guardTemplate_rel_iff` | faithful | — |
| template-height-certificate | `heightTemplate`, `heightBuild_formula` | faithful | — |
| template-library | `templateLibrary`, `templateLibrary_witnesses`, `templateLibrary_wf` | faithful; templates refer to callees as terms, not indices, so "denoted in this order" holds by construction | — |
| template-log25 | `log25Template`, `log25Template_rel_iff` | faithful | — |
| template-multiply | `multiplyTemplate`, `multiplyBuild_formula` | faithful (generator point `genPoint 15 = (0, X₁₅, −145, X₁₆, X₁₇)`) | — |
| template-natural | `naturalTemplate`, `naturalBuild_formula` | faithful | — |
| template-pole | `poleTemplate`, `poleTemplate_poly` | faithful | — |
| template-raw-inverse-x | `rawInverseXTemplate`, `rawInverseXTemplate_rel_iff` | faithful; the meaning "$v=1/x(p)$, $0$ at $O$" is `rawInverseXTemplate_rel_iff_field` (unlisted) | — |
| template-raw-z | `rawZTemplate`, `rawZTemplate_rel_iff` | faithful; the meaning is `rawZTemplate_rel_iff_field` (unlisted) | — |
| template-signed-encode | `signedEncodeTemplate`, `signedEncode_facts` | faithful | — |
| template-slope | `slopeTemplate`, `slopeBuild_formula` | faithful | — |
| template-test-group | `testGroupTemplate`, `testGroupBuild_formula` | faithful | — |
| template-value-test | `valueTestTemplate`, `valueTest_facts` | faithful; $2730^6$ is `pow_six_2730` (unlisted) | — |

## Remarks

**R1. `translate_rel_iff` carries an unused (PV).** Its hypothesis `hpow : PowerSetup recipes
power P N` has four fields: `wf`, `witnesses`, `present` and `spec`. The field `spec` is (PV) for
the power recipe. The proof uses only `wf` and `witnesses`, through `translate_scopedIn_library`.
The article's relational form assumes only a well-formed power recipe, and the composition
`modelRecipe_rel_iff _ _ _ (translate_scopedIn hwf … hpw)` proves it as stated. The consumers
(model-evaluation semantics, soundness, completeness) all assume (PV), so nothing downstream is
affected. Suggestion: either add a variant without `spec` (taking `wf` and `witnesses` only) and
list it, or add `ZInQ.Translation.translate_scopedIn` to the article's `lean:` field.

**R2. Exact count of the precision recipe.** Under `HaltingNodeCheck`,
`precisionCircuit_nodeStats` gives the exact counts (54,056 explicit variables, 125,327 / 98,382
/ 15,845 add / mul / call nodes). With `precisionCircuit_counts`, the exact count of 292,889,492,861
variables would follow from `translate_variableCount` in a few lines. No consumer needs it.

**R3. Incomplete `lean:` lists** (claims proved under unlisted names). The rows above name the
unlisted declarations for:
- natural-circuit-values, natural-circuit-well-formed, model-recipe-relation;
- fixed-constants, least-formal-multiple, prime-catalogue, primorial-literal;
- literal-polynomial, builder-soundness;
- template-raw-z, template-raw-inverse-x, template-value-test.

**R4. Stale sentence outside the re-check scope.** `syntax/division-polynomial-multiplication.md`
ends with "Its formal proof is a substantial project independent of this manuscript". The
proposition is proved (`ZInQ.mulByN_formulas`, model chapter). The article and its Lean are
unchanged since the previous audit, so I left it. The lead may want to drop the sentence.

**R5. Lean docstring nit.** The docstring of `Compiler/Translation/WellFormed.lean` cites
`nodeVal_congr`, but the lemma is `nodeVals_congr`. Not changed, since this task does not edit
Lean files.

## Method

- Every article's statement was read against the Lean source of its `lean:` declarations.
- Elaborated types were read from a scratch `#check @name` file over all 200 names. One Lean
  process ran at a time, with load below 50. The scratch file was deleted.
- Numeric claims were compared against the Lean literals and `…_facts` / `…_run` statements:
  block starts, counts, the primorial literals and the witness arithmetic.
- No Lean file was edited.
