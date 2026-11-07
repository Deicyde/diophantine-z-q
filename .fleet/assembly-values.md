# Task assembly-values: report

Value templates of the assembly chapter (`blueprint/roadmap/assembly/value-templates/`).
Lean modules: `ZInQKernel/Assembly/Values/*.lean`, root `ZInQKernel/Assembly/Values.lean`
(imported by `ZInQKernel.lean`). Namespace `ZInQ.Assembly`. No `sorry`, no axioms beyond
`propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms`), no `native_decide`.
Merged branches: `wip/nat-translation` (M and the natural-code predicate), `wip/assembly-local`
(its definition of `Test`), `wip/syntax-recipes` (the outer recipes).

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| `assembly/value-templates/double-and-add-chains.md` | `ZInQ.Assembly.chain_value`, `chain_satisfiable`, `chainBuild_binDigits_value`, `chainCount_contacts` (file `Values/Chains.lean`) | proved |
| `assembly/value-templates/six-local-tests.md` | `ZInQ.Assembly.Test` (defined by assembly-local in `Assembly/Local/SixLocalTests.lean`); bridge `ZInQ.Assembly.test_iff` (file `Values/Tests.lean`) | definition reused; bridge proved |
| `assembly/value-templates/signed-encoding-semantics.md` | `ZInQ.Assembly.signedEncode_rel_iff` (`Values/SignedEncode.lean`) | proved |
| `assembly/value-templates/close-coordinates-semantics.md` | `ZInQ.Assembly.closeCoordinates_rel_iff` (`Values/Close.lean`) | proved |
| `assembly/value-templates/exceptions-semantics.md` | `ZInQ.Assembly.exceptions_rel_iff` (`Values/Exceptions.lean`) | proved |
| `assembly/value-templates/value-test-semantics.md` | `ZInQ.Assembly.valueTest_rel_iff` (`Values/ValueTest.lean`) | proved |
| `assembly/value-templates/outer-recipe-relations.md` | `ZInQ.Assembly.close_rel_iff`, `main_rel_iff`, `valueUnion_rel_iff`, `value_rel_iff`; for the specification `spec_close_rel_iff`, `spec_main_rel_iff`, `spec_valueUnion_rel_iff`, `spec_value_rel_iff` (`Values/Outer.lean`) | proved |

## Statements and corrections

- **Hypotheses.** The articles for the signed encoding and the value test assume H, PC and 22P.
  In Lean these theorems take only the multiplication statement M,
  `Translation.MultiplicationExact I cstar ell T` (as the task instructions require). H, PC and
  22P enter only through M, which the multiplication chapter derives from them. The theorems are
  generic in the constructors `I` and the constants `cstar ell T` of the templates.
- **Double-and-add chains.** The chain is the template's `chainBuild out base ds`, stated for an
  arbitrary build state and digit list. Soundness: if `out = ι(a)`, `base = ι(m)` and all raw
  additions hold, the value is `ι(a + binVal ds · m)`. With `out = O` and `ds = binDigits k`
  this is `ι(k m)`. Completeness (`chain_satisfiable`) is stated as: if `out` and `base` have
  their variables below the counter, the fresh points can be chosen without changing any variable
  below the counter. That locality is what the exceptions proof needs. The raw-addition count is
  `chainCount`, with `(chainBuild …).1.2.length = chainCount ds` and the values 0, 7, 6, 6, 8, 9
  for the six contacts (`chainCount_contacts`, closed by `rfl` on the digit lists).
- **Six local tests.** assembly-local had already defined `Test` (with `Mult.zCoord`,
  `Mult.wCoord` and rational casts), so per the instructions I use its definition.
  `Values/Tests.lean` defines the forms the template computes: `wPt` (`w = 1/x`, `0` at `O`),
  `vtD`, `vtR0`, `vtA0`, `vtR`, `vtW` and `vtTheta`. These use `Compiler.Precision.zPt` and
  `algebraMap ℚ K₀`. `test_iff` proves that they give exactly `Test`. Both definitions match
  the article, with `Θ = Tr(W⁻¹)` written as `QuadraticAlgebra.trace`.
- **Coordinate window.** `r(a, j)` is `Compiler.Precision.rRatio a j` and `ε_l` is `epsIdx l`.
  Both are built from `zIdx`, which takes the value 0 at index 0, as the article requires.
- **Exceptional values.** `𝒞` is `Compiler.Precision.contacts : Finset ℤ`. The conclusion is
  `∃ c ∈ contacts, N = ι(c) ∧ t = c`.
- **Outer recipes.** The recipes are `CompositionRecipe` data whose callee parameter counts are
  not definitionally fixed. Relations are therefore stated on value lists:
  `ValRel τ [v₀, v₁, …] := τ.Rel (fun k => l.getD k 0)`, in the style of `Translation.CodeRel`.
  `valRel_ofFn_iff` converts these to `Rel` at a vector. The general theorems take any
  template library and earlier recipes, with the callees' well-formedness and witness counts as
  hypotheses (the callee recipe's count is the parameter `w`). The `spec_*` versions instantiate
  them for `specLib I cstar ell T c3 Nc`, with every template callee rewritten to the
  template-level `Rel` (`signedEncodeTemplate`, `closeTemplate`, `valueTestTemplate`,
  `exceptionsTemplate`, `memberTemplate`). One wording point: the article's item 1 lists the
  calls as `Rel_{signed_encode}(Σᵢ, Eᵢ)`; in Lean these are the five separate conjuncts in the
  order N, K, A, L, J.

## Lemmas added beyond the leaves

- `Values/Lift.lean`: `lift_iff_holds_of_callees_nil`, which says `φ^* = φ` for call-free
  formulas. Also lifted forms of `feq`, `peq`, `fin`, `NZ`, `Z`, `IX`, `Div` and `POS`, the call
  atoms of `member` and `raw_add` on codes (`lift_member_call`, `lift_rawAdd_code`), and
  `iota_apply_zero_eq_zero_iff`. The last one says the first coordinate of `ι(m)` is 0 exactly
  when `m ≠ 0`.
- `Values/Gadgets.lean`: the gadgets on canonical codes, `holds_zFormula_iota`
  (`[ζ] = z_m`, plus the inverse witness when `m ≠ 0`) and `holds_ixFormula_iota`
  (`[v] = w([m]P₀)`). Also `holds_divFormula_iff`, `exists_zsmul_genP0_eq_some` (nonzero
  multiples are affine with `x, y ≠ 0`), `codeNormY_iota_ne_zero`, and the assignment writer
  `writeVals` with its read-back lemmas.
- `Values/SignedEncode.lean`: `enc_natCast`, `enc_neg_succ`, and the parameter read-back
  lemmas.
- `Values/ValueTest.lean`: `val_slopeW` (the pair product `W` in field terms), `ev_valueContact`,
  `lift_pole_call` and `lift_multiply_code`.
- `Values/Outer.lean`: `compositionRecipe_rel_iff`, the private-witness lemma for an arbitrary
  composition recipe whose arguments lie below a bound `B` and whose blocks lie at or above `B`
  and are disjoint. Also `lift_recipeCall` and `map_point`.

## Problems

- The first snapshot of `wip/nat-translation` that I merged did not compile
  (`NaturalCode.lean`). The next push fixed it, and it is merged now.
- assembly-local defined `contactPoly`, `testD`, `testR` and `Test` in `ZInQ.Assembly` while I
  was working. I renamed my value-test forms (`vt*`) to avoid the clash and bridged them with
  `test_iff`.
- `valueTest_rel_iff` needs `set_option maxHeartbeats 4000000`. Its completeness direction reads
  about 65 witness values back from an explicit list with `simp`. The whole file elaborates in
  about 35 s.

## Suggestions for the next agent

- The ordinary-value relation can now be assembled. Combine `spec_value_rel_iff`,
  `spec_valueUnion_rel_iff`, `spec_main_rel_iff` and `spec_close_rel_iff` with
  `exceptions_rel_iff`, `valueTest_rel_iff`, `signedEncode_rel_iff` and
  `closeCoordinates_rel_iff`. The precision callee is `getEx (specLib …) 1`, whose relation
  belongs to the compiler chapter (C). After that, `exists_zero_integers_iff` links the result
  to `P_*`.
- Converting between `ValRel` on `List.ofFn` concatenations and `Rel` at `Fin.append` vectors
  works with `List.ofFn_fin_append` and `valRel_ofFn_iff _ rfl _`; see `valRel_signedEncode` etc.
- The article's notation for close (`Rel_close(N, K, t)`) uses the list
  `ofFn N ++ (ofFn K ++ [t])` in `spec_close_rel_iff`, which is right-associated. Use
  `List.append_assoc` when matching it with `main`.
