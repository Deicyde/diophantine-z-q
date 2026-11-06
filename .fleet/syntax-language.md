# syntax-language: report

Task: the existential-polynomial framework (blueprint chapter `syntax/`, the expression
language). Modules are in `ZInQKernel/Syntax/Language/`, the root module is
`ZInQKernel/Syntax/Language.lean`, and `ZInQKernel.lean` imports it. Everything is in namespace
`ZInQ.Syntax`. There is no `sorry`, `axiom` or `native_decide`. The main theorems depend only
on `propext`, `Classical.choice` and `Quot.sound` (checked with `#print axioms`).
`lake build ZInQKernel` succeeds.

**Push status: blocked.** Every `git push` and `git ls-remote` to github.com failed with
"Recv failure: Connection reset by peer". Retrying through the host's `fwdproxy:8080` got
"CONNECT tunnel failed, response 403". All work is committed locally on branch
`wip/syntax-language` in `~/dzq-wt/syntax-language` (six commits on top of `8b7aed6`, this
report included) and still needs to be pushed.

## Modules

| Module | Contents |
| --- | --- |
| `Basic` | `Poly`, `ev`, `VarsIn`/`VarsLT`, `ExPoly` (params, witnesses, poly), `assign`, `ExPoly.Rel`, `callSubst`/`callPoly`/`ExPoly.call`, `blockUpdate`, degree of substitution, `exists_fin_rename` |
| `Formula` | `Formula` (eq / atom / call / and / or), `compile`, `Holds`, sum-of-squares semantics, `atoms`, `degree` and degree bounds |
| `Lifting` | blocks, free polynomials, `Lift`, `Scoped`, private witness blocks |
| `PointRef` | `pointRef`, `generatorConstraints`, `codeP0`, `codeNegP0`, generator values |
| `Nodes` | `Constructors`, `Node`, `Template`, node, library and recipe denotations, recipes as formulas |
| `Gadgets` | inverse witnesses, pair norm, positivity and absolute value over `ℚ` |
| `Build` | the construction monad `Build`, `Build.template`, rational constants, `NZ`, `POS`, relation, WF and degree lemmas for constructed templates |
| `Pairs` | pair and point-code formulas, `Pair.val` into `K0`, field-pair arithmetic |
| `Size` | ℓ¹ coefficient norm `l1` with compositional bounds |

## Leaves

| Article | Lean name(s) | Status |
| --- | --- | --- |
| syntax/template-semantics.md | `Constructors`, `Node`, `Template`, `Node.denote`, `denoteNodes`, `Template.denote`, `denoteLibrary`, `callPoly`, `ExPoly.call`, `ExPoly.Rel`, `Connective`, `CallTarget`, `RecipeCall`, `CompositionRecipe`, `Operation`, `ModelRecipe`, `Recipe`, `Recipe.poly`, `Recipe.denote`, `denoteRecipes` | proved (definitions) |
| syntax/sum-of-squares-semantics.md | `Formula.ev_compile_eq_zero_iff`, `ev_sum_sq_eq_zero_iff`, `ev_prod_eq_zero_iff` | proved |
| syntax/nonzero-gadgets.md | `exists_mul_eq_one_iff`, `eq_one_div_of_mul_eq_one`, `pairNorm_eq_zero_iff`, `pairNorm_ne_zero_iff`, `K0_mk_eq_zero_iff`, `K0_ne_zero_iff_pairNorm`, `exists_mul_pairNorm_eq_one_iff`; gadget form `exists_update_nzFormula_iff`, `exists_update_fnz_iff` | proved |
| syntax/field-pair-arithmetic.md | `Pair.val`, `Pair.val_add/neg/sub/smul/mul/sq/pow/one/zero/ofInt/conj`, `Pair.C_ev_norm`, `Pair.val_A`, `Pair.val_delta`, `holds_feq`, `exists_update_fnz_iff`, `exists_update_divFormula_iff`, `exists_update_zFormula_iff`, `holds_ixFormula`, `not_isO_and_fin`, `holds_curve` | proved |
| syntax/language/formula-compilation.md | `Formula`, `Formula.compile`, `Formula.Holds`, `BuildState`, `Build`, `Build.fresh`, `Build.freshIdx`, `Build.call`, `Build.rational`, `globalEq`, `Build.template`, `Build.nz`, `Build.pos`, `nzFormula`, `posFormula` | proved (definitions); node encoding not done, see below |
| syntax/language/call-semantics.md | `ev_callPoly`, `ExPoly.ev_call`, `ExPoly.exists_blockUpdate_call_iff` | proved |
| syntax/language/existential-lifting.md | `Formula.exists_blocks_iff` (also `Formula.exists_holds_iff`, `Formula.lift_congr`) | proved |
| syntax/language/rational-constants.md | `ev_globals_eq_zero_iff`, `generator_values`, `codeP0_coordinates`, `compile_globals_nil` | proved |
| syntax/language/positivity-gadget.md | `pos_iff_four_squares`; gadget form `exists_blockUpdate_posFormula_iff` | proved |
| syntax/language/absolute-value-gadget.md | `eq_abs_iff_four_squares` (with `exists_four_squares_of_nonneg`) | proved |
| syntax/language/field-pair-gadgets.md | `Pair` and `Pair.add/neg/sub/smul/mul/sq/pow/powAux/ofInt/one/zero/conj/norm/A/delta`, `feq`, `Build.fnz`, `Build.fdiv`, `divFormula`, `Code`, `Code.O/neg/x/y`, `peq`, `isO`, `fin`, `curve`, `Build.freshPoint`, `Build.gen`, `Build.zGadget`, `zFormula`, `ixFormula` | proved (definitions) |
| syntax/language/point-references.md | `pointRef`, `pointRefList`, `generatorConstraints` | proved (definitions) |
| syntax/language/generator-references.md | `pointRef_eval_generator`, `generatorConstraints_eq_zero_iff` | proved, with explicit codes (see below) |
| syntax/language/builder-soundness.md | — | not done (skipped as instructed: optional JSON cross-check) |
| syntax/language/builder-well-formed.md | — | not done (skipped as instructed: optional JSON cross-check) |

## Statement corrections and deviations

1. **template-semantics.** The constructor nodes cannot be given meaning here: fixed integer
   expressions, `Ψ_{n,c}` and `G_T` belong to other chapters. So `Node E` is parametric in the
   type `E` of fixed expressions, and every denotation takes a record
   `I : Constructors E` with `val : E → ℤ`, `psi : ℤ → Fin 2 → MvPolynomial (Fin 4) ℤ` and
   `guard : ℤ → MvPolynomial (Fin 15) ℤ`. A `psi`/`guard` node denotes `bind₁` of the argument
   node polynomials into `I.psi (I.val e) c` / `I.guard (I.val e)`. This is the article's
   definition with `Ψ` and `G` as polynomials in 4 and 15 variables; the guard variables are
   numbered `0..14`, not `1..15`.
   - Templates and recipes denote an `ExPoly` with parameter count `p`, witness count `v - p`
     (truncated) and polynomial.
   - Out-of-range node, template or recipe references are read as `0` or as the empty
     `ExPoly ⟨0,0,0⟩`. A model recipe with a kind-2 operation and no power recipe uses the empty
     `ExPoly`.
   - Names, metadata and `witnessBlocks` are omitted (they carry no constraint).
   - Recipe constraints are defined as the compilations of conjunct formulas
     (`RecipeCall.formula`, `ModelRecipe.conjuncts`). These are the same polynomials (atoms
     compile to themselves, call atoms to the call polynomial; `RecipeCall.constraint_eq`).
     This gives `Recipe.poly_eq_compile` for free.
2. **formula-compilation.**
   - `Formula` has a tagged call atom `call τ g w` that compiles to `τ[g; w]`, besides the
     generic atom `⟨f⟩`. This is how the existential-lifting article reads call atoms; the
     generic atom is kept.
   - Constructions are programs in a state monad `Build` (counter and global equations), not
     the free monad `Prog` with three interpreters suggested by the notes. Witness counts are
     computed by the kernel with `decide`/`rfl`; a 16-witness test program with calls,
     rational constants and gadgets reduced instantly.
   - Squares are written `t ^ 2`, which is the same polynomial as `t * t`.
   - `Build.rational u 0` records the equation `0·X = u`; the JS throws instead. The lemmas
     assume `q ≠ 0`.
   - **The node encoding (hash-consed node list of a constructed template) is not
     formalized.** It only fixes syntax heights and the cross-check. All degree and coefficient
     bounds here are on polynomials.
3. **existential-lifting.** Stated with `y : ℕ → ℚ` agreeing with `x` outside the blocks,
   instead of `y` on `⋃ B_i`; the two are equivalent.
   - Generic atoms `⟨f⟩` are allowed and treated like `a ≐ b`: they must avoid the blocks and
     are read as `f(x) = 0`.
   - The hypotheses are `Formula.Scoped`: callees well formed, `blocks` pairwise disjoint as a
     list, free polynomials avoiding all blocks.
   - The remark "both sides depend only on `x` outside the blocks" is `Formula.lift_congr`.
4. **rational-constants.** Proved for `q_i ≠ 0` (the article has `q_i ≥ 2`). The `P₀`
   coordinates are stated in `K0` as `codeP0_coordinates`.
5. **generator-references.** The article says `ref(-2)(x) = ι(1)` and `ref(-3)(x) = ι(-1)`, but
   `ZInQ.iota`/`pointCode`/`genP0` (model chapter) do not exist on this branch. The theorem
   therefore gives the explicit values `codeP0 = (0, 1641/8, -145, -15465/4, 87483/32)` and
   `codeNegP0`. The model chapter should prove `iota 1 = codeP0` and `iota (-1) = codeNegP0`.
6. **nonzero-gadgets, positivity-gadget.** The gadget statements are about the formula at an
   explicit fresh index `c`, assuming the fresh variable(s) do not occur in `a`. The article
   leaves this implicit. The variables are `X_c` for `NZ` and the block `X_c..X_{c+3}` for
   `POS`.
7. **field-pair-arithmetic.**
   - `σ` is `star` on `QuadraticAlgebra ℚ 2 0` (with `b = 0` it is `(re, -im)`).
   - `[k u] = k [u]` is stated for any polynomial `k` as `C (ev x k) * [u]`.
   - Parts 3–5 are stated for the formulas at explicit fresh indices with "fresh variable does
     not occur" hypotheses.
   - `Div(n, d)` is stated for an arbitrary quotient pair `q`. By `Build.fdiv_apply` the
     construction uses `q = (X_c, X_{c+1})` and inverse-norm variable `X_{c+2}`.
   - `p = O` is read as "the values of `p` are `(1,0,0,0,0)`"; no canonical-code assumption is
     needed.
8. **point-references.** References below `-3` (never used) are read as five zeros.

## Lemmas added beyond the leaves

- Variable ranges:
  - `VarsIn` (all variables satisfy `P`) with closure lemmas; `VarsLT` is its specialization.
  - `mem_vars_callPoly`, `VarsLT.callPoly`, `ExPoly.varsLT_call`, `Formula.varsLT_compile`,
    `Formula.mem_vars_compile`, `VarsLT.connective`.
  - `Build.template_wf`, `Build.template_varCount`.
- Degrees: `totalDegree_bind₁_le` (not in Mathlib), `totalDegree_callPoly_le`,
  `totalDegree_list_sum_le`, `totalDegree_sum_sq_le`, `Formula.degree` with
  `Formula.totalDegree_compile_le`, `Formula.totalDegree_compile_and_le`/`_or_le`,
  `Build.totalDegree_template_le`, `totalDegree_connective_*`.
- Coefficients (`Size`):
  - `l1`, `natAbs_coeff_le_l1`, `l1_add_le`, `l1_sub_le`, `l1_mul_le`, `l1_pow_le`.
  - List and finset sum/product bounds, `l1_sum_sq_le`.
  - `l1_bind₁_le` (`l1 P · B^deg P`), `l1_callPoly_le`, `l1_rename_of_injective`.
  - `Formula.normBound` with `Formula.l1_compile_le`.
- Final renaming: `exists_fin_rename`. A polynomial with variables below `N` is `rename Fin.val Q`
  with equal coefficients, `deg Q ≤ deg P`, and `eval₂ (Int.castRingHom ℚ) v Q = ev (extendFin v) P`.
  This matches the shape of `FrozenTarget`.
- Relations:
  - `ExPoly.rel_iff_exists_assignment`.
  - `ExPoly.rel_iff_exists_lift`: the relation of an `ExPoly` whose polynomial is a scoped
    formula is the lifted formula at some assignment extending the parameters.
  - `Build.template_rel_iff`.
- Recipes and libraries:
  - `CompositionRecipe.formula`, `ModelRecipe.formula`, `Recipe.formula`,
    `Recipe.poly_eq_compile`. Existential lifting therefore applies directly to recipes.
  - `getD_foldl_snoc`, `getPoly_denoteNodes`, `getEx_denoteLibrary`, `getEx_denoteRecipes`.
- Construction simp lemmas: `Build.bind_apply`, `pure_apply`, `fresh_apply`, `freshIdx_apply`,
  `call_apply`, `rational_apply_new/old/one`, `nz_apply`, `pos_apply`, `fnz_apply`,
  `fdiv_apply`, `zGadget_apply`, `freshPoint_apply`.
- Points: `holds_peq`, `holds_isO`, `holds_fin`, `holds_curve`, `evCode`, `holds_zFormula`.

## Problems

- Pushing to GitHub is blocked from this host (see the top). Nothing else blocked the work;
  load and memory stayed under the limits.
- The `Build` monad has no general well-scoping invariant (that would be the
  builder-well-formed article). Each template proves well-formedness with `Build.template_wf`
  from its unfolded final state, using the `VarsLT`/`VarsIn` closure lemmas.

## Suggestions for the next agents

- **Template chapters.**
  1. Write each template as a `Build Formula` program.
  2. Unfold it with the `*_apply` simp lemmas (`Build.bind_apply`, `Build.fresh_apply`,
     `Build.call_apply`, the gadget lemmas, `Build.rational_apply_new`/`_old`).
  3. Prove the relation with `Build.template_rel_iff`, or with `ExPoly.rel_iff_exists_lift`
     plus `Formula.exists_blocks_iff` when the template has calls.
  4. Witness counts: `decide` on `(Build.template p prog).witnesses = m`.
- **Constants and division-polynomial chapters.** Instantiate `Constructors FixedExpr` with
  `val`, `Ψ_{n,c} ∈ MvPolynomial (Fin 4) ℤ` and `G_T ∈ MvPolynomial (Fin 15) ℤ`.
- **Model chapter.** Prove `iota 1 = codeP0` and `iota (-1) = codeNegP0` to finish
  generator-references as the article states it.
- **Size chapter.** Use `totalDegree_callPoly_le` and `l1_callPoly_le` for calls,
  `totalDegree_sum_sq_le`/`l1_sum_sq_le` and `totalDegree_list_prod`/`l1_list_prod_le` for
  connectives, `Formula.degree`/`Formula.normBound` for formulas, and `exists_fin_rename` for
  the final move to `Fin 292890231905`. `natAbs_coeff_le_l1` turns an ℓ¹ bound into the
  per-coefficient bound of `FrozenTarget`.
- **Optional.** If the JSON cross-check or syntax heights are wanted, add a node-encoding
  interpreter for `Build` (hash-consed node list) and prove it agrees with `Template.denote`
  (builder-soundness).
