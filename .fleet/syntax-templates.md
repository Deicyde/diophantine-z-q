# Report: syntax-templates

Branch `wip/syntax-templates`. Modules under `ZInQKernel/Syntax/Templates/` (`Scope`, `Member`,
`Core`, `Certificate`, `Multiply`, `Value`, `Library`), root `ZInQKernel/Syntax/Templates.lean`,
imported from `ZInQKernel.lean`. No `sorry`, no axioms beyond `propext`, `Classical.choice`,
`Quot.sound` (checked with `#print axioms` on the library theorems); no `native_decide`.
`lake build ZInQKernel` succeeds.

## Status

All names are in namespace `ZInQ.Syntax`. For every template `fooTemplate : ExPoly` there are
`fooTemplate_params`, `fooTemplate_witnesses` (the counts of
`construction/ordinary-integer-definition.json`), `fooTemplate_wf` and `fooTemplate_rel_iff`.
Templates with calls also have `foo_facts` (block list = the JSON `witnessBlocks`, counter,
constants, scope) and `fooBuild_formula` (the built formula equals an explicit formula with the
article's variables).

| Article | Lean name | Status |
| --- | --- | --- |
| syntax/template-member.md | `memberTemplate` (`memberBuild`, `memberFormula`, `memberTemplate_poly`, `memberTemplate_rel_iff`) | proved |
| syntax/template-raw-add.md | `rawAddTemplate` (`rawAddBuild`, `rawAddFormula`, `addOut`, `rawAddTemplate_poly`, `rawAddTemplate_rel_iff`) | proved |
| syntax/templates/template-library.md | `templateLibrary`, `integerConstants`, `length_templateLibrary`, `templateLibrary_params`, `templateLibrary_witnesses`, `templateLibrary_wf`, `getEx_templateLibrary_scalar` | proved |
| syntax/templates/template-abs.md | `absTemplate` (`absFormula`, `absTemplate_poly`; `absTemplate_rel_iff : Rel (x, a) ↔ a = abs x`) | proved |
| syntax/templates/template-raw-z.md | `rawZTemplate` (`rawZTemplate_poly`, `rawZTemplate_rel_iff`, `rawZTemplate_rel_iff_field`) | proved |
| syntax/templates/template-raw-inverse-x.md | `rawInverseXTemplate` (`_poly`, `_rel_iff`, `_rel_iff_field`) | proved |
| syntax/templates/template-log25.md | `log25Template`, `Pair.log25`, `log25Coeffs` (`log25Template_poly`, `_rel_iff`) | proved |
| syntax/templates/template-pole.md | `poleTemplate`, `polePolyOf`, `polePolyX` (`poleTemplate_poly`, `ev_polePolyX`) | proved |
| syntax/templates/template-slope.md | `slopeTemplate`, `slopeBuild`, `slopeFormula`, `slope_facts`, `slopeBuild_formula` | proved |
| syntax/templates/template-test-group.md | `testGroupTemplate`, `testGroupBuild`, `testGroupFormula`, `testGroup_facts`, `testGroupBuild_formula` | proved |
| syntax/templates/template-height-certificate.md | `heightTemplate`, `heightBuild`, `heightFormula`, `height_facts`, `heightBuild_formula` | proved |
| syntax/templates/template-guard.md | `guardTemplate` (`guardTemplate_poly`, `guardTemplate_rel_iff : Rel ↔ G_T(a) ≠ 0`) | proved |
| syntax/templates/guard-semantics.md | `guardTemplate_rel_iff_not_falseTriple`, `FalseTripleCodes`, `codes3`, `eval₂_distanceProduct_eq_zero_iff` | proved, with the zero set of `G_T` as a hypothesis (see corrections) |
| syntax/templates/template-multiply.md | `multiplyTemplate`, `multiplyBuild`, `multiplyFormula`, `genPoint`, `multiply_facts`, `multiplyBuild_formula` | proved |
| syntax/templates/template-fixed-scalar.md | `scalarTemplate`, `scalarFormula`, `psiPair` (`scalarTemplate_poly`, `_rel_iff`) | proved |
| syntax/templates/template-natural.md | `naturalTemplate`, `naturalBuild`, `naturalFormula`, `natural_facts`, `naturalBuild_formula` | proved |
| syntax/templates/template-signed-encode.md | `signedEncodeTemplate`, `signedEncodeBuild`, `signedEncodeFormula`, `signedEncode_facts` | proved |
| syntax/templates/template-close-coordinates.md | `closeTemplate`, `closeBuild`, `closeFormula`, `close_facts` | proved |
| syntax/templates/template-value-test.md | `valueTestTemplate`, `valueTestBuild`, `valueTestFormula`, `valueTest_facts` | proved |
| syntax/templates/template-exceptions.md | `exceptionsTemplate`, `exceptionsBuild`, `exceptionBranch`, `fixedMultipleBuild`, `chainBuild`, `binDigits`, `exceptions_facts` | proved |

Two articles outside my list are also done, because they were free:
`syntax/templates/pole-semantics.md` is `poleTemplate_rel_iff : poleTemplate.Rel a ↔ PoleSoluble (a 0)`,
and `syntax/templates/log25-coefficients.md` is `log25Coeffs_spec` (by `decide`).

## What "relation" means here

* Templates without calls: `fooTemplate_poly : poly = (fooFormula …).compile ^ 2` and
  `fooTemplate_rel_iff : Rel a ↔ ∃ y, (fooFormula …).Holds (assign p m a y)`.
* Templates with calls: `fooTemplate_rel_iff : Rel a ↔ ∃ y : ℕ → ℚ, (∀ i, y i = a i) ∧
  [constants take their values] ∧ (fooFormula …).Lift y`. Here `Lift` replaces every call atom
  by the callee relation (`Formula.Lift`), so these are the private-block statements that the
  semantic chapters need (e.g. natural-semantics: unfold `naturalFormula` with
  `Formula.lift_and`, `Formula.lift_call`, `ev_comp_append`, `ev_varPoint`).

## Statement corrections and design decisions

1. **ExPoly, not node lists.** Templates are `ExPoly`s built with the framework's
   `Build.template`. The node encoding (`Template E`, hash-consed node lists, root indices
   149, 308, …) is not built. The library is a `List ExPoly`, which is what `Recipe.denote`,
   `ModelRecipe.conjuncts` etc. take as `templates`. "Every call refers to a template of
   smaller index" holds by construction (callees are embedded `ExPoly` terms of earlier
   definitions) and is not stated separately.
2. **Fixed constants as integer values.** The framework keeps fixed expressions abstract
   (`E`, `I : Constructors E`). The templates take `I` (for `Ψ` and `G`) and the *values*
   `val(e) : ℤ`:
   `scalarTemplate I n` is `S_e` for `n = val(e)`;
   `guardTemplate I T`, `multiplyTemplate I cstar ell T`, `naturalTemplate I cstar ell T`, …;
   `templateLibrary I cstar ell T c3` uses `integerConstants c3 = [4, 2, 3, c3, 1399]`.
   To instantiate, pass `I.val cstarExpr` etc. The index expressions `e + 1`, `e + (-1)`,
   `2·e` of `S_e` become `n + 1`, `n + -1`, `2 * n`. **The constants task must prove that
   `val` evaluates `add`/`mul` this way** if it wants to link `S_e` to a node-level encoding.
3. **guard-semantics needs `G_T`.** `G_T` is defined by the constants chapter (guard-product
   article, not mine). `guardTemplate_rel_iff_not_falseTriple` takes as hypothesis
   `hG : ∀ P, eval₂ P (I.guard T) = 0 ↔ FalseTripleCodes T P`. The step of the article's proof
   sketch that is independent of the false triples is `eval₂_distanceProduct_eq_zero_iff`: a
   product over a list of factors `Σ_j (D_t X_j - c_{t,j})²` with `D_t ≠ 0` vanishes exactly at
   the points `c_{t,·}/D_t`. Once `G_T` is defined as such a product over the false triples,
   `hG` follows from it, from the reduced-fraction coordinates of `ι(a)`, and from
   injectivity of `codes3`.
4. **Expression shapes.** Polynomials are written with `a - b`, `u ^ 8`, `3 * e * H`, … where the
   JS DAG has `a + (-1)·b`, repeated squaring, `3·(e·H)`. They are equal in `MvPolynomial ℕ ℤ`,
   which is all that `ExPoly` records. The pole polynomial follows `ZInQ.polePoly` exactly,
   so `ev_polePolyX` is `rfl` after unfolding, without `ring`.
5. **Block order in exceptions.** `Build.Facts` lists blocks in formula order. For
   `value.exceptions` the formula is `⋀(member[N], ⋁(β…))`, so `exceptionsBlocks` starts with
   `(405, 7)` and then lists the 36 raw additions `(14 + 11i, 6)`. The JSON lists the same
   blocks in allocation order. For every other template the two orders agree.
6. **Explicit formulas.** Every template with calls except `value.exceptions` has an explicit
   formula with the article's indices, proved equal to the built one (`*_formula`). For the
   exceptions, the 36 chain calls are pinned only by `exceptionsBlocks`, the counter, the
   constants and `binDigits_contacts`. The relation is stated with
   `(exceptionsBuild (varPoint 0) (X 5) ⟨6, []⟩).1.Lift y`.
7. pole: the polynomial is `(polePolyX - 0)^2`, because the atom `B S ≐ 0` compiles to
   `B S - 0`. abs: the polynomial is written `(a - (z₁² + ⋯ + z₄²))² + …`.
8. The article for `log25` says `δ^j` is computed by successive multiplication and `ζ^{4j+1}`
   by repeated squaring. `Pair.log25Aux` does both, with the framework's `Pair.pow`.

## Lemmas and tools beyond the leaves (all in `Scope.lean` unless noted)

* Variable predicates: `Avail N B` (below `N`, outside blocks `B`; decidable via `blockFree`),
  `PairIn`, `CodeIn`, `ArgsIn`, `FOk` (callees well formed, free polynomials in `G`, blocks below
  `N`), with structural lemmas, and `blocks_*` lemmas for the gadget formulas.
* Weakest preconditions for `Build`: `Build.WP` and rules `wp_bind`, `wp_pure`, `wp_fresh`,
  `wp_freshIdx`, `wp_freshPair`, `wp_freshPoint`, `wp_point`, `wp_freshPoints`,
  `wp_freshPairs`, `wp_call`, `wp_nz`, `wp_fnz`, `wp_pos`, `wp_fdiv`, `wp_zGadget`,
  `wp_rational`, `wp_gen`. Tactics: `wp_step G N` / `wp_run G N` (dispatch on the program
  head), `scope` (structural proof of `FOk`/`PairIn`/`CodeIn`/`ArgsIn`/`VarsIn` goals; it also
  applies local ∀-hypotheses and splits `∀ i : Fin n` goals), `facts_close`.
* `Build.Facts p b N B GE` (counter, block list, global equations, scope facts) with
  `Facts.of_wp`, `Facts.wf`, `Facts.witnesses`, `Facts.rel_iff`, `Facts.rel_iff_nil`, and
  `Build.template_rel_iff_lift` (the relation of a constructed template through its private
  blocks, from `ExPoly.rel_iff_exists_lift`).
* Allocation primitives with the same allocation as the JS: `Build.point` (as
  `Build.freshPoint`, returning `varPoint c`), `Build.freshPoints n`, `Build.freshPairs n`,
  `Build.freshPair`. Argument helpers: `varPoint`, `varPair`, `varArgs`, `codesArgs`,
  `pairsArgs`, `Pair.args`. Evaluation: `ev_varPoint`, `ev_varPair_fst/snd`, `ev_varArgs`,
  `ev_comp_append`.
* `Build.mapL` (unused by the final templates), `slopeW` with `PairIn.slopeW`,
  `VarsIn.polePoly`, the pole pieces `poleM`, `poleH`, `poleT1`, `poleT2`, `poleBS`.
* Field-level semantics `rawZTemplate_rel_iff_field` and `rawInverseXTemplate_rel_iff_field`
  (`Core.lean`). `pow_six_2730 : 2730^6 = 413976684737889000000` (`Value.lean`).

## Problems met

* Plain `rfl`/`decide` on counts or formulas of a template that calls a big template
  (natural → multiply → height_certificate → slope → test_group) recomputes the callee builds
  and hits deep recursion in the elaborator and the kernel. The fix is the WP run: it takes
  each callee's witness count from its lemma (`hm : τ.witnesses = m`), so no proof evaluates a
  callee build. Explicit formulas are proved by `dsimp only [build, Build.bind_apply,
  Build.call, …]`, then `simp only [*_witnesses]`, then `rfl`.
* `rw [Build.call_apply]` fails on calls whose arguments have type `Fin (5+5+5) → Poly`,
  because the term is not type-correct at reducible transparency against
  `Fin τ.params → Poly`. `dsimp only [Build.call]` works.
* `GL` is Mathlib notation; `λ` cannot be an identifier.

## Suggestions for the next agent

* natural-semantics, multiplication and assembly: use `naturalTemplate_rel_iff`,
  `multiplyTemplate_rel_iff`, … with the explicit formulas, then `Formula.lift_and`,
  `Formula.lift_call`, `ev_comp_append`, `ev_varPoint` to get callee relations at explicit
  points. `rawAddTemplate_rel_iff` and `memberTemplate_rel_iff` are stated with `Holds` at
  `assign`. The model chapter can start from them, or from `holds_*` lemmas of the framework.
* constants task: instantiate with `I.val`. Prove `val (add e (lit 1)) = val e + 1` etc. if
  needed, and give `G_T` with its zero-set lemma (via `eval₂_distanceProduct_eq_zero_iff`) to
  discharge `hG`.
* New templates: write a `Build` program, then prove
  `Build.Facts.of_wp ?_ (by decide) (by decide) (by decide) (by decide)`. Put each callee's
  `_wf` and `_witnesses` lemmas in context with `have`, then run
  `wp_run (Avail N B) N; facts_close`. Lists, `match` on concrete data, `let` and user helper
  builds are unfolded automatically. Avoid `if` on data in programs (use `match`). Prove a
  `PairIn`/`VarsIn` lemma for large pure helpers (e.g. `slopeW`, `polePolyOf`) and add it with
  `have` so that `scope` uses it instead of unfolding.
* The cross-check against the saved JSON (node lists, randomized identity test) is still
  external. Counts and block lists are checked in Lean against the JSON numbers.
