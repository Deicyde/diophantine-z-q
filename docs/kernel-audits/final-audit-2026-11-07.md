# Final audit of the assembled proof (task final-audit)

Scope: the claim that `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_nodeCheck`
(`ZInQKernel/Main.lean:25`) proves `ZInQ.FrozenTarget` from the four hypotheses H, PC, 22P, CAT
and the named finite check `ZInQ.Compiler.Universal.HaltingNodeCheck`. Audited at commit
`e49d5da` (branch `wip/final-audit` = `origin/main`), with `lake build ZInQKernel` succeeding
(9473 jobs). Its only `sorry` warning is `ZInQKernel/Main.lean:34:8`, the four-hypothesis
theorem.

## Verdict

**I found nothing that makes the conditional main theorem false or vacuous, or that makes it
something other than the frozen statement.** Its type is literally
`HaltingNodeCheck → SixContactEstimate → PoleCompleteness → FixedPrimePattern → CatalogueBound → FrozenTarget`.
Its axioms are `propext`, `Classical.choice` and `Quot.sound`. `FrozenTarget` is the frozen
upstream statement: syntactically equal as an `Expr`, not merely definitionally equal.

The witness is `specPstar ↑c3`. The zero projection and the size bounds are about that same
polynomial and the same template library. Every hypothesis is a true statement as far as can
be checked, and none is stronger than the manuscript. `HaltingNodeCheck` is true by native
evaluation (independently replayed here). Its kernel proof is the one missing piece.

The findings below are about how the claim is *presented*: a fifth hypothesis that the
top-level blueprint articles do not mention, and lesser record drift.

## Findings, by severity

### Severity 1: false, vacuous, or not the frozen statement

None.

### Severity 2: hidden hypotheses

**F1. The proved theorem has a fifth hypothesis, `HaltingNodeCheck`, which no kernel proof
discharges yet. The top-level articles state four hypotheses.**
- In Lean the hypothesis is visible in the type, so this is not hidden at the Lean level.
- The four-hypothesis theorem `exists_bounded_integer_polynomial_defining_integers_of`
  (`Main.lean:34`) is `sorry` (axioms include `sorryAx`). The only `lean:` field of
  `main/main-theorem.md` points to it. The article records no `proof:` field, which is honest.
- These articles state their result over at most the four hypotheses, with
  `proof: formalized`, but their Lean theorems also take `hN : HaltingNodeCheck`:
  - `assembly/assembly-lemma.md`: `Pstar_spec`, `assembly`.
  - `size/syntax-bounds.md`: `Pstar_size`, `Pstar_target_bounds`.
  - `syntax/recipes/fin-variable-form.md`: `specPstar_spec`, `specPstar_zero_projection`.
- `syntax/recipes/witness-accounting.md`: `vars_integers_lt` and
  `specIntegers_variableCount_le` take `PrecisionShape N c3`. For the concrete circuit this
  comes from `precisionShape_of hN` (`Syntax/Recipes/Literal.lean:50`).
- The dependency is recorded only indirectly, through `circuit-node-counts.md` →
  `halting-node-check.md`. That article correctly has `statement: formalized` and no `proof:`.
- Truth of the check today:
  - The task node-check (`origin/wip/node-check`, commit `10bd0a5`, not merged into main) proves
    `haltingNodeCheck_of_checkB : haltingNodeCheckB = true → HaltingNodeCheck`, a verified fast
    builder plus a Boolean counter.
  - It closes `haltingNodeCheckB = true` with `native_decide` in a separate library
    `ZInQFinite`, which `ZInQKernel` never imports.
  - Until a kernel proof lands, the truth of the fifth hypothesis rests on the Lean compiler
    (plus the external transcription script mentioned at `Compiler/Universal/NodeCheck.lean:14`).
- Replay in this audit (evidence, not proof): I copied the four node-check modules into a
  scratch file over current main. The soundness lemma compiles, with axioms
  `[propext, Classical.choice, Quot.sound]`, and the evaluations print:
  ```
  #eval haltingNodeCheckB                                   -- true
  #eval countGo (fastNodesRev interpreter 204 2) 0 0 0 0 []  -- (54049, 6, 125307, 98361, [0, 1, 2, 4, 1399, -1])
  ```
  These are exactly the five conjuncts of `HaltingNodeCheck`.

**Recommendation:**
- In the four articles above, state the check as an explicit hypothesis, or mark their proofs
  as conditional on `halting-node-check.md`.
- Add `exists_bounded_integer_polynomial_defining_integers_of_nodeCheck` to the `lean:` field
  of `main/main-theorem.md`. Today it is recorded only in the implementation note
  `af_0be94ccf3fca69a8d9322f8c.md`.

### Severity 3: statement drift (Lean against article)

**F2. `assembly/assembly-lemma.md`.** Article: "Assume H, PC, 22P, CAT. Then P_* satisfies
1–3." Lean `Pstar_spec (hN) (hH) (hPC) (h22) (hCAT)` (`Assembly/Top/Assembly.lean:54`) has
the extra `hN` (F1). Otherwise identical:
- `P_*` is `specPstar (c3 : ℤ)`;
- conclusions 1–3 are the three conjuncts of `FrozenTarget`, verbatim;
- `assembly` packages them as `FrozenTarget`.

`Pstar_spec_of` additionally isolates the dependence on H, PC, 22P through the single premise
`hval` (the projected value relation). This is a refinement, not drift.

**F3. `main/main-theorem.md`.** The statement matches the sorry'd theorem exactly. The proved
variant is not recorded (F1).

**F4. `syntax/recipes/witness-accounting.md`.**
- The article states the full seven-row table. Lean proves:
  - row power_value exactly (`powerValueRecipe_variableCount = 17786718`);
  - the precision bound (`precisionRecipe_variableCount_le`, under `PrecisionShape`);
  - the exact consecutive differences (`specClose_witnessCount`, `specMain_witnessCount`,
    `specValueUnion_witnessCount`, `specValue_witnessCount`, `specIntegers_variableCount`,
    in `Syntax/Recipes/Accounting.lean:84–137`);
  - `specIntegers_variableCount_eq : … = 739069 + (specPrecision N c3).witnessCount` and the
    bound `≤ 292890231905`.
- The table therefore follows, but most of its row lemmas are not in the `lean:` field.
- All the count theorems are generic in `(N, c3)`, and the bounds need `PrecisionShape N c3`.
  The article's statement does not mention that the bounds depend on the node statistics
  (only its proof dependencies do; see F1).
- "Every variable … below its variable count" is `specLib_wf` (`ExPoly.WF`). Faithful.

**F5. `syntax/recipes/fin-variable-form.md` and `size/syntax-bounds.md`**
(lean fields audited under item 1):
- `specPstar_zero_projection` and `Pstar_target_bounds` take `HaltingNodeCheck` (F1).
- `Pstar_target_bounds` is stated for any `c3 : ℤ` with `c3.natAbs < 2^(2^24)`. The assembly
  discharges this for the actual literal by `c3_lt' : c3 < 2 ^ 2 ^ 24` (`c3_natAbs_lt`,
  `Assembly/Top/Assembly.lean:24`). Harmless generalization.

**Faithful, no drift:**
- **`assembly/ordinary-value-relation.md`:** `value_relation_iff`, `exists_value_relation_iff`
  (`Assembly/Top/ValueRelation.lean:86,94`) state exactly `Rel_value(N,t) ⟺ ∃ n, N = ι(n) ∧ t = n`
  and its projection.
  - Hypotheses are H, PC, 22P (no CAT, no node check), as in the article.
  - `Rel_value` is `ValueRel`, recipe 5 of `closeSpecLib` = `specLib specConstructors c_* ℓ T ↑c3 (precisionCircuitOf ↑c3)`.
    The article leaves this specialization implicit.
- **`multiplication/multiplication-template.md`:** `multiplication_exact` (`Multiplication/Top/Exact.lean:25`)
  states `MultiplicationExact specConstructors c_* ℓ T`, i.e. for all `p q r ∈ ℚ⁵`,
  `Rel_multiply(p,q,r) ⟺ ∃ a b, p = ι a ∧ q = ι b ∧ r = ι(ab)`.
  - Uniqueness is `multiplication_exact_unique` and `multiplication_existsUnique`.
  - The parameter count 15 is forced by the type of `Fin.append (Fin.append p q) r`; the
    witness count 35,134 is `multiplyTemplate_witnesses`. Neither is restated in the theorem.
  - The split of hypotheses matches the article: soundness `multiply_sound hH`, completeness
    `multiply_complete hPC h22`.
- **`compiler/natural/natural-polynomial-semantics.md`:** `natural_polynomial_semantics'`
  (`Compiler/Universal/WrapperCode.lean:149`) states
  `(∃ z : Fin 1305806 → ℕ, eval (natPoint 5 1305806 c z) (precisionCircuit.poly powerTemplate) = 0) ↔ accepts c`.
  - The article's prose `accepts` matches `Precision.accepts_iff` (`Compiler/Precision/Relation.lean:47`).
  - No height, RC or node-check premise, as the article says.
  - `precisionCircuit = precisionCircuitOf ↑c3` by `rfl` (checked), so this is the same
    circuit the assembly uses.

### Severity 4: cosmetic

- **F6.** `KERNEL_PLAN.md` (finite-computations table) says milestone 1 checks
  `HaltingNodeCheck` "by `native_decide` in the separate library `ZInQFinite`". On main
  `ZInQFinite` does not exist yet: it is on `origin/wip/node-check` only, and `lakefile.toml`
  on main declares only `ZInQKernel`.
- **F7.** The docstring of `Compiler/Universal/NodeCheck.lean` says the check "was checked
  outside Lean by a transcription". It will need updating when the node-check branch lands.
- **F8.** `c3` is an `irreducible_def` (`Compiler/Universal/WrapperCode.lean:27`). `#print`
  shows `c3 := wrapped✝.1`, an `opaque` constant created by the macro. This is the one
  non-tactic `opaque` in the sweep (see item 5). It is harmless, but "the concrete program
  literal" is concrete only through `c3_def : c3 = code wrapper`.

## Evidence by item

### 1. Axioms

Scratch file `scratch/final-audit/Axioms.lean` (deleted before commit):
- `import ZInQKernel`;
- `#print axioms` for the main theorems and for **all 80 names** in the `lean:` fields of
  `assembly/**` (27 articles), `multiplication/multiplication-template.md`,
  `compiler/natural/natural-polynomial-semantics.md`, `syntax/recipes/*` (10 articles) and
  `size/syntax-bounds.md`;
- a memoized sweep over **every constant declared in a `ZInQKernel.*` module** (18,411
  constants), mirroring `Lean.CollectAxioms`.

Output (80 of 80 names reported; the lines not shown all read `[propext, Classical.choice, Quot.sound]`):
```
'ZInQ.exists_bounded_integer_polynomial_defining_integers_of_nodeCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.exists_bounded_integer_polynomial_defining_integers_of' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'ZInQ.Assembly.chainCount_contacts' does not depend on any axioms
'ZInQ.Syntax.closeRecipe' / mainRecipe / valueUnionRecipe / valueRecipe / integersRecipe / witness_count_arith / variable_count_arith: does not depend on any axioms
constants in ZInQKernel modules: 18411
union of axioms: [Quot.sound, Classical.choice, sorryAx, propext]
axiom declarations: []
opaque constants: [ZInQ.Size.Tac.applyThen, ZInQ.Size.Tac.unfoldSubject, ZInQ.Size.Tac.tryLemmas,
 ZInQ.Syntax.Build.scopeGoal, ZInQ.Compiler.Universal.wrapped._@…WrapperCode…, ZInQ.Size.Tac.sizeGoal]
constants with nonstandard axioms (1): [(ZInQ.exists_bounded_integer_polynomial_defining_integers_of, [sorryAx])]
```
`HaltingNodeCheck` itself: `[propext, Classical.choice, Quot.sound]`.

Greps over `ZInQKernel/` (393 files):
- `sorry`: only `Main.lean:37`. `admit`, `native_decide`, `implemented_by`, `extern`,
  `axiom` declarations, `unsafe`, `@[csimp]`, `ofReduceBool`, `trustCompiler`, `addDecl`,
  `modifyEnv`, `debug.*`, the option that skips kernel checking: **none**. `#eval`, `run_cmd`, `run_elab`: none.
- `opaque`: none in source. The sweep's opaque constants are the five `partial def` tactic
  functions and the `irreducible_def` wrapper of `c3`.
- `partial`: only meta-level tactic code (`Size/Majorants/Tactic.lean:102,117,130,140`,
  `Syntax/Templates/Scope.lean:884`). Their outputs are proof terms re-checked by the kernel.
- **Every `set_option` besides linters** (none weakens kernel checking):
  - `maxHeartbeats` (`Assembly/Values/ValueTest.lean:84` 4000000; `Compiler/Programs/Blocks.lean:349`
    and `Compiler/Programs/PrecisionCorrect.lean:394` 2000000; `Compiler/Translation/PowerScope.lean:36`
    0): elaborator budget only.
  - `maxRecDepth` 20000/100000 (`Size/Constants/Closed.lean:37,57`, `Size/Constants/Small.lean:34`,
    `Syntax/Templates/Multiply.lean:219,307`, `Syntax/Templates/Certificate.lean:350`,
    `Syntax/Templates/Value.lean:101,311,471`, `Compiler/Circuits/PowerTemplateNodes.lean:14`,
    `Compiler/Translation/PowerScope.lean:35`, `Compiler/Universal/NodeCheck.lean:83`,
    `Syntax/Recipes/PowerValue.lean:31`): elaborator recursion limit only.
  - `exponentiation.threshold` 512–9100 (`Size/Constants/{Closed,Small,T,D,Catalogue,FormalMultiple}.lean`):
    lets the elaborator's `Nat.pow` evaluation warning threshold rise; it does not affect the kernel.
  - `hygiene false` (`Compiler/Circuits/Counts.lean:157,186`, `MacroSemantics.lean:131,137,155`,
    `Builder.lean:321,330,346`, `Scope.lean:179`, `Compiler/Universal/Grows.lean:160`,
    `WrapperSize.lean:70`): macro name hygiene for the tactic macros that follow.
  - Linter options (`linter.unusedSimpArgs`, `unusedTactic`, `unreachableTactic`,
    `unnecessarySeqFocus`): warnings only.
- **Macros and elabs:** all are tactic macros (`counts_tac`, `poly_simp`, `vars_tac`,
  `isnat_tac`, `mono_tac`, `valid_tac`, `triple_tac`, `regs_ext`, `omegaJ`, `upd`,
  `frame_scratch`, `pres_tac`, `aomega`, `grows_tac`, `fsem_simp`, `exec_simp`, `zexec_simp`,
  `zcond_simp`, `sl_simp`, `block_tac`, `fixed_val`, `wp_run`, `facts_close`) or tactic elabs
  (`size`, `size_maj`, `size_le`, `scope`, `wp_step`).
  - None is a term or command elaborator, so none can hide a term in a statement.
  - Notations are local (`HVP`, `T₀`, `T₁`, `Y₀–Y₂`) or infix sequencing (`;;`, `;;;`).
    None appears in the main theorem or the hypotheses.

### 2. The target

```
$ python3 scripts/check_target.py
FrozenTarget matches lean/Frozen/BoundedIntegerPolynomial.lean
```
- `scratch/final-audit/Frozen.lean` imports exactly the frozen file's four Mathlib imports
  plus `ZInQKernel.Target`, and elaborates the frozen statement's text verbatim (namespace
  `ZInQ`) as `FrozenCopy`. Comparing the two values as `Expr`s prints
  `syntactically identical values: true`.
- `#print` with `pp.fullNames`/`pp.explicit` shows `hyperoperation` is Mathlib's root
  `hyperoperation`, with no `ZInQ.` shadowing.
- `lean/Frozen/BoundedIntegerPolynomial.lean` is unchanged since upstream commit `f7475ae`
  (`git log -- lean/Frozen/…`).
- `scratch/final-audit/Main.lean` telescopes the type of each main theorem and compares the
  body with `Lean.mkConst ``ZInQ.FrozenTarget`:
  ```
  exists_bounded_integer_polynomial_defining_integers_of_nodeCheck: 5 binders [HaltingNodeCheck, SixContactEstimate, PoleCompleteness, FixedPrimePattern, CatalogueBound]; conclusion == FrozenTarget: true
  exists_bounded_integer_polynomial_defining_integers_of: 4 binders [SixContactEstimate, PoleCompleteness, FixedPrimePattern, CatalogueBound]; conclusion == FrozenTarget: true
  ZInQ.Assembly.assembly: 5 binders [...]; conclusion == FrozenTarget: true
  ```

### 3. The hypotheses

**No change since `docs/kernel-audits/hypothesis-audit.md`.**
- `git diff 8ee01d5 HEAD -- ZInQKernel/Hypotheses ZInQKernel/Target.lean lean/Frozen scripts/check_target.py`
  touches only `Hypotheses/MordellWeil.lean`, and only its module docstring (MW became a
  theorem in `c248f3b`).
- The definitions of `SixContactEstimate`, `PoleCompleteness`, `FixedPrimePattern` and
  `CatalogueBound` are byte-identical to the audited ones. The earlier verdicts therefore
  stand. I re-read them against the manuscript:

| Hypothesis | Manuscript | Satisfiable as stated? | No stronger than manuscript? |
| --- | --- | --- | --- |
| `SixContactEstimate` (`Hypotheses/Height.lean:95`) | Thm 4.1, tex:377–410 | Yes. Constants, domain (`S ⊇ {p ≤ 324}` finite set of primes, real `R ≥ max(D, max S, 10¹²)`) and `M_S(u)` match symbol for symbol. `contactSupport` has no junk value off `𝒞` (`prime_dvd_contactSupport_iff`), and `M_S ≥ 1` (empty product), so the right side is never accidentally `0`. | Yes, verbatim. |
| `PoleCompleteness` (`Hypotheses/Pole.lean:39`) | Thm 5.2, tex:972–1003 | Yes. `polePoly` matches `Q_pole` term by term. `B > 0` rules out the `padicValRat p 0` junk value. No trivial obstruction: `|m| ≥ 1 > B`, so `H = A(A − B²) ≠ 0` is possible. | Yes, verbatim. |
| `FixedPrimePattern` (`Hypotheses/PrimePattern.lean:106`) | Prop 6.2, tex:1267–1296 | Yes. `𝓗`, `𝓚` carry no `Nat.nth` junk (`cataloguePrime_spec`, `pos_of_mem_catalogueMultipliers`). There is no local obstruction: the 22 forms in `(u_j, v)` can be made to avoid `q⁵ ∣` for every `q ≤ 324` by a residue choice, and good primes exist (`goodPatternPrime_seventeen`). | Yes: it omits the extra facts the proof gives (`p ≡ 1 mod 8`, `p ≡ 3 mod 7`). |
| `CatalogueBound` (`Hypotheses/PrimePattern.lean:115`) | Prop 12.1 proof, tex:6285–6303 | Yes, true: BMOR gives more than `X/(2W⁴) > 22` primes in each unit class below `X = 2^(W³)`, none `≤ 324`. | Yes: it asks for 22, the manuscript gives more. |
| `HaltingNodeCheck` (`Compiler/Universal/NodeCheck.lean:103`) | blueprint `halting-node-check.md` item 1 | Yes. True by the native evaluation of the node-check branch and by the replay above (F1). It is a closed decidable proposition about the explicit construction `haltingCircuit`. It mentions no hypothesis, no `c3` and no large constant. | Matches item 1. The Lean definition states 4 counts and the constant list; the total `293568`, the call count `15845` and the first two nodes are proved from it (`haltingCircuit_nodeStats`, `haltingCircuit_countKind_call`, `haltingCircuit_nodes_eq`). So the Lean check is weaker than item 1 and item 1 follows from it. |

### 4. The witness

From `#print` in `scratch/final-audit/Main.lean`:
```
theorem ZInQ.Assembly.assembly … :=
fun hN hH hPC h22 hCAT => Exists.intro (ZInQ.Syntax.specPstar ↑ZInQ.Compiler.Universal.c3) (ZInQ.Assembly.Pstar_spec hN hH hPC h22 hCAT)
def ZInQ.Syntax.specPstar := fun c3 => ZInQ.Syntax.Pstar (precisionCircuitOf c3) c3
def ZInQ.Syntax.Pstar := fun N c3 => PstarOf specConstructors FixedConst.cstar.value FixedConst.ell.value FixedConst.T.value c3 N
@[reducible] def ZInQ.Assembly.closeSpecLib := specLib specConstructors FixedConst.cstar.value FixedConst.ell.value FixedConst.T.value ↑c3 (precisionCircuitOf ↑c3)
def ZInQ.Syntax.specConstructors := { val := FixedConst.fixedVal, psi := psiComponent, guard := guardPoly }
```
These `example`s were checked by `rfl`:
- `specPstar ↑c3 = PstarOf specConstructors c_* ℓ T ↑c3 (precisionCircuitOf ↑c3)`;
- `closeSpecLib = specLib specConstructors c_* ℓ T ↑c3 (precisionCircuitOf ↑c3)`;
- `precisionCircuit = precisionCircuitOf ↑c3`.

How each conjunct reaches that polynomial:
- **Zero projection:**
  - `specPstar_zero_projection_valueRel` (`Assembly/Top/Assembly.lean:29`) is about
    `specPstar ↑c3`. It rewrites with `specPstar_zero_projection`, whose
    `valueExPoly specConstructors c_* ℓ T ↑c3 (precisionCircuitOf ↑c3)` is
    `getEx (specLib …) 5`.
  - It closes with `valRel_ofFn_iff` against `ValueRel = ValRel (getEx closeSpecLib 5)`. This
    type-checks only because the two libraries are the same term.
- **Degree and coefficients:** `Size.Pstar_target_bounds hCAT hN c3_natAbs_lt`, whose
  conclusion is about `specPstar c3` with the implicit `c3 := ↑Compiler.Universal.c3`, the
  same polynomial.
- `PstarNat_maj` uses `integers_maj` on `PstarNat (precisionCircuitOf c3) c3`, which is
  `PstarNatOf specConstructors c_* ℓ T c3 _`. That is the same library: `specPstar_spec`
  relates it to `specPstar c3`.

There is no library mismatch.

### 5. Definitions that could trivialize statements

General point: the conclusion `FrozenTarget` mentions none of the project's definitions, and
the five hypotheses mention only the definitions in `Hypotheses/` and `NodeCheck.lean`. An
internal definition with a junk value could at worst make the *proof* fail, and the kernel
accepted the proof. It cannot weaken the theorem. Case by case:
- **`leastFormalMultiple`** (`Syntax/Constants/FormalMultiple.lean:164`, `sInf`, `0` if empty;
  then `M0`, `cstar`):
  - A definite natural number, though not computable.
  - The witness polynomial depends on it, which is legitimate for an existential statement.
  - A junk value `0` would break the multiplication proofs, not the statement.
- **`catalogueProduct`, `catalogueMax`, `Syntax.cataloguePrime`** (`Syntax/Constants/Catalogue.lean:43–52`,
  `Nat.nth`): definite values. No junk, by Dirichlet (`infinite_catalogue_class`). Used only
  inside the witness and its proofs.
- **`ZInQ.cataloguePrime`** in the hypotheses (`Hypotheses/PrimePattern.lean:23`, `Nat.nth`):
  no junk (`cataloguePrime_spec`); audited in `hypothesis-audit.md`.
- **`contactSupport`, `pointCount`** (hypotheses): `Classical` only for decidability and
  `Nat.card`; characterized by `prime_dvd_contactSupport_iff` and `pointCount_eq_card`.
- **`c3`** (`irreducible_def`, F8): an opaque wrapper with equation `c3_def`. The kernel cannot
  unfold `c3`, so no proof can rely on a computed value except through `c3_def`. `c3_lt'`
  bounds it.
- **`orderAbove`** (`Size/FormalMultiple/ReductionOrders.lean:173`, `Classical.choose`): used
  only inside proofs of the size chapter. Its spec is `orderAbove_spec`.
- **`packedAssign`** (`Compiler/Circuits/Packed/Polynomial.lean:413`), the `θ₀` in
  `Compiler/Translation/Soundness.lean:176`, and `Nat.find` in `Packed/Sound.lean:156`: witness
  assignments built inside proofs.
- **Well-founded recursion with used equations:**
  - `FixedConst.value` (`Syntax/Constants/Fixed.lean:203`, `WellFounded.Nat.fix`, then irreducible);
  - `TapeLists` (`Compiler/Interpreter/TapeLists.lean:86,203`), `ScalarMul` (`Compiler/Precision/ScalarMul.lean:27`),
    `FormalGroupLaw` (`Multiplication/Local/FormalGroupLaw.lean:35`), `Pairs` (`Syntax/Language/Pairs.lean:64`);
  - structural-with-`decreasing_by` recursion in `Hierarchical`, `Formula` and `Lifting`.
  - All equations come from Lean's equation lemmas, which are proved, so this is sound. The
    only risk with WF definitions is that kernel evaluation is impractical. No statement
    relies on evaluating them. `HaltingNodeCheck` is evaluated through the verified fast
    builder of the node-check branch, not by unfolding.
- **Structures with `Prop` fields** (`Program.Valid`, `PackedConditions`, `Spec*`, `WellScoped`,
  `WellFormed`, `TranslationShape`, `CalleeSemantics`, `PowerSetup`, `PrecisionShape`, …):
  - They appear only as premises of intermediate lemmas.
  - The main theorem's type has exactly the five hypotheses above, so every such premise is
    discharged inside the kernel-checked proof term. None is assumed.
- **`attribute [irreducible]`** (`Ps … T`, `catalogue`, `S_b`, `S_mul`, `searchQ`,
  `tripleCode`, `leastFormalMultiple`, `cataloguePrime`, `catalogueProduct`, `catalogueMax`,
  `FixedExpr.val`/`valMax`; `@[irreducible] powerTemplatePoly`): elaborator-only
  transparency. The kernel ignores it.

### 6. Blueprint against Lean (top level)

See F1–F5. Summary:

| Article | Lean | Differences |
| --- | --- | --- |
| assembly/assembly-lemma.md | `Assembly.Pstar_spec`, `Assembly.assembly` | extra hypothesis `HaltingNodeCheck` (F1, F2); otherwise verbatim |
| assembly/ordinary-value-relation.md | `Assembly.value_relation_iff`, `Assembly.exists_value_relation_iff` | none (specialization to `closeSpecLib` implicit in the article) |
| multiplication/multiplication-template.md | `Mult.multiplication_exact`, `_unique`, `_existsUnique` | none (counts 15 / 35,134 not restated in the theorem; enforced by types and `multiplyTemplate_witnesses`) |
| compiler/natural/natural-polynomial-semantics.md | `Compiler.natural_polynomial_semantics`, `'` | none |
| main/main-theorem.md | `exists_bounded_integer_polynomial_defining_integers_of` (sorry) | statement identical; the proved five-hypothesis variant is unrecorded (F1, F3) |
| syntax/recipes/witness-accounting.md | `specRecipes`, `specLib`, `specLib_wf`, `specIntegers_variableCount_eq/_le`, `vars_integers_lt` | table rows proved under unlisted names; bounds conditional on `PrecisionShape`, i.e. on the node check (F4) |

## Scratch files

`scratch/final-audit/{Axioms,Frozen,Main,NodeCheckReplay}.lean`. They were deleted before the
final commit, and no Lean file outside them was changed.
