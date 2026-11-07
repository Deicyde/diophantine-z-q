# Report of task nat-translation

Chapter `blueprint/roadmap/compiler/translation/`. Lean namespace `ZInQ.Translation`, directory
`ZInQKernel/Compiler/Translation/`, root module `ZInQKernel/Compiler/Translation.lean` (imported by
`ZInQKernel.lean`). Every leaf is proved. None uses `sorry`, `axiom` or `native_decide`.
`#print axioms` on the main theorems shows only `propext`, `Classical.choice` and `Quot.sound`.

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| `lagrange-four-squares.md` | `four_squares` (FourSquares.lean) | proved |
| `natural-circuit-values.md` | `nodeVal`, `circuitValue`, `templateValue`, `callValue`, `callTemplate`, `circuitPoly`, `Admissible`; `circuitValue_eq_eval_poly`, `nodeVal_eq_eval` (Values.lean) | proved (definitions and the evaluation identity) |
| `natural-circuit-well-formed.md` | `WellFormedCore`, `WellFormed`, `HasCall`; locality: `nodeVals_congr`, `circuitValue_congr`, `circuitValue_congr_lt`, `nodeVal_update_block` (WellFormed.lean, Soundness.lean) | defined; lemmas proved |
| `natural-code-semantics.md` | `MultiplicationExact` (the statement M, a `Prop`), `natural_rel_iff` (NaturalCode.lean) | proved |
| `model-recipe-relation.md` | `translate_rel_iff` (TranslateSemantics.lean); generic form `modelRecipe_rel_iff` with `ModelHolds` (RecipeRelation.lean) | proved |
| `translation-soundness.md` | `translate_sound` (Soundness.lean) | proved |
| `translation-completeness.md` | `translate_complete`, witness assignment `TranslationShape.witness` (Completeness.lean) | proved |
| `model-evaluation-semantics.md` | `translate_rel_iff_zero`, `translate_rel_iff_value` (TranslateSemantics.lean); shape forms `TranslationShape.rel_iff_zero`, `TranslationShape.rel_iff_value` (ModelSemantics.lean) | proved |
| `power-value-semantics.md` | `powerValue_rel_iff`, `powerValue_spec` (PowerValue.lean) | proved |
| `precision-circuit-scope.md` | `precisionCircuit_wellFormed` (PrecisionScope.lean), `powerTemplate_wellFormed` (PowerScope.lean) | proved |
| `rational-translation.md` | `precision_rel_iff`, `precision_rel_iff_accepts_of` (Rational.lean) | proved |

## Statement corrections and precisions

1. **M is parametric.** The templates on main are parametric in the constructors `I` and the
   constants `c_*, ℓ, T`, so `MultiplicationExact I cstar ell T` is too. Statement:
   `∀ p q r, (multiplyTemplate I cstar ell T).Rel (Fin.append (Fin.append p q) r) ↔ ∃ a b, p = ι a ∧ q = ι b ∧ r = ι (a*b)`.
   The multiplication chapter should prove exactly this `Prop`.
2. **Division-polynomial constructors.** Every semantic statement (natural-code predicate
   excepted) also assumes `hI : I.psi = psiComponent`. This is the hypothesis of the fixed-scalar
   semantics of syntax-recipes (`scalarTemplate_rel_iff_iota`). It is not a mathematical
   hypothesis. It records that the constructors are the concrete ones; once a concrete
   `Constructors` exists, it is `rfl`.
3. **Relational form and model-evaluation semantics need well-formedness.** The article states
   the relational form for any translated circuit. The witness-scope proof (`translate_scopedIn`)
   uses distinct explicit-variable indices and arguments that point to earlier nodes. On
   ill-formed input the total `Syntax.translate` writes the reference `-4`. Both Lean statements
   also need:
   - the constant table `consts` to be a prefix of `integerConstants c3` that contains the
     nontrivial constants of the circuit;
   - a `PowerSetup` for the power recipe: well formed, its witness count recorded, present when
     the circuit has call nodes, and satisfying (PV).
4. **Values.** The call value reads `θ_{w+i-3}` for every `i ≥ 3`, with no cut-off at `V_𝒫`.
   This agrees with the article under well-formedness (`templateValue_congr_of_core`).
   Assignments are `θ : ℕ → ℤ`, and admissibility means nonnegativity.
5. **(PV)** is `PowerValueSpec π P`, stated on lists of codes:
   `CodeRel π [ι a, ι b, ι c, r] ↔ ∃ w : Fin (V_𝒫 - 3) → ℕ, r = ι (T_𝒫 (blockAssign P a b c w))`.
   The power-value article's form with `Fin.append` and `w : Fin 79 → ℕ` is
   `powerValue_rel_iff`, and `T` is `powerValueT`.
6. **Rational translation.** The precision recipe calls `power_value` as recipe `0`
   (`Syntax.precisionRecipe`). The statement therefore assumes the recipe library has recipe `0`
   equal to `power_value` denoted over some earlier recipes (`hrec`). The five codes are
   `E : Fin 5 → Fin 5 → ℚ`, with parameters `k ↦ E (k/5) (k%5)`. The zero `C(c, z) = 0` is
   `MvPolynomial.eval (natPoint 5 1305806 c z) (precisionCircuit.poly powerTemplate) = 0`,
   the same form as nat-halting's `natural_polynomial_semantics'`. The corollary with the
   precision relation takes (C.4) as a hypothesis `hC4`, because nat-halting's (C.4) still has
   a `sorry` (wrapper correctness).
7. **Well-formed, condition 6:** block variables are bounded pointwise:
   `∀ i ∈ [w, w+V_𝒫-3), i < V`.
8. **Precision-circuit scope is proved by construction, with no 293,620-node check:**
   - argument order: `ℋ`'s node list is well formed by the builder's soundness
     (`haltingCircuit_nodesWF`), and the 52 appended nodes refer only to earlier nodes;
   - explicit variables are below `V`: the scope invariant `ScopeInv` (`haltingCircuit_vars_lt`);
   - their indices are distinct by counting: with the 15,845 blocks of 79 they cover
     `1,305,804 = 54,049 + 15,845·79` variables (`nodup_of_cover`, `haltingCircuit_vars_nodup`);
   - constants: `precisionCircuitOf_consts` and `c3_gt`.

   The power-template part is one Boolean kernel check, `powerTemplateCheck_eq_true`
   (`decide +kernel` on the 474 nodes, about 25 s).

## Lemmas and definitions beyond the leaves

- `Points.lean`: `writePoints` and `pointAt` (writing points into an assignment), with the
  read-back lemmas.
- `Spec.lean`: `TranslationShape`, the facts about a translated recipe used by soundness and
  completeness; also `CalleeSemantics`, `PowerValueSpec`, `blockAssign` and `Slot`.
- `TranslateShape.lean`: `translateShape` shows that `Syntax.translate` of a well-formed circuit
  has that shape. The proof is an augmented fold that records allocations (`Alloc`, `AllocInv`,
  `VarInv`, `NodeInv`), plus `formulaBlocks`, a permutation of the allocated blocks.
- `RecipeScope.lean`, generic model recipes:
  - `blocks_formula`: the call blocks of a model recipe;
  - `vars_freePolys`: free variables are generator variables or coordinates of used references;
  - `mem_callees_formula`, `callees_wf_formula`.
- `TranslateScope.lean`: `translate_scopedIn`, the witness-scope theorem of
  `syntax/language/builder-well-formed.md` for the model-evaluation translation (call blocks
  disjoint and above the parameters, references and atoms avoiding them, variables below the
  variable count). syntax-recipes confirmed they would not prove it.
- `Library.lean`:
  - `calleeSemantics_library`: the natural, raw-addition, multiply and `S_c` callees of
    `templateLibrary` under M and `hI`;
  - `getEx_library_scalar`, `library_witnesses`;
  - `codeArgs_one` … `codeArgs_four`.
- `RecipeRelation.lean`: `ScopedIn`, `rel_iff_lift` (relation of a compiled formula through
  private blocks), `CodeRel`, `refVal`.
- `PrecisionScope.lean`: `nodup_of_cover`, `haltingCircuit_nodesWF`, `haltingCircuit_vars_lt`,
  `haltingCircuit_vars_nodup`, `specialize_nodesWF`, `specialize_root_lt`.
- `Rational.lean`: `callTemplate_powerTemplate`, `circuitValue_precision`,
  `denote_wf_of_scopedIn`, `precision_powerSetup`.

## Problems

- **The full build stops in another task's file.** After merging `wip/syntax-recipes` and the
  later `wip/nat-halting`, `lake build ZInQKernel` fails at
  `ZInQKernel/Syntax/Recipes/Literal.lean:56` (owned by syntax-recipes). nat-halting's
  `precisionCircuitOf_explicitVars` gained a conjunct (`∀ v ∈ rest, v.2 = .witness`), and
  `precisionShape_of` still destructures `⟨rest, -, h⟩`. The fix is
  `obtain ⟨rest, -, -, h⟩ := precisionCircuitOf_explicitVars code`. I did not edit that file.
  Every Translation module builds, and so does everything else. My last commit was made with
  this one failure outstanding.
- `WellFormed` has no `Decidable` instance. Its fields are stated with unbounded quantifiers over
  node membership. No consumer needs decidability: the scope is proved by construction.

## Suggestions for the next agent

- When a concrete `Constructors` with `psi = psiComponent` exists, discharge `hI` by `rfl`.
  Instantiate `MultiplicationExact` with the multiplication chapter's theorem.
- The assembly should build the recipe library with `power_value` at index `0` (as
  `precisionRecipe` assumes) and discharge `hrec`. It can then use
  `precision_rel_iff_accepts_of` with `natural_polynomial_semantics'` once wrapper correctness is
  proved.
- Fix `Literal.lean:56` as above, so that the merged tree builds.
- Blueprint `lean:` fields: use the names in the table above.
