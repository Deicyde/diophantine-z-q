# rv-compiler-translation: adversarial review report

Reviewed: `blueprint/roadmap/compiler/README.md`, `compiler/translation/` (12 leaves),
`compiler/translation/machine/` (23 leaves), their notes, and
`blueprint/sources/compiler-translation-locators.md`, against manuscript lines 5745-6093
(Section 10 opening and Sections 10.1-10.4), Section 3.1 (lines 350-371), Section 4 constants
(lines 381-399, 968), Section 11 (lines 6094-6125, 6230-6256), Section 12 (lines 6372-6381),
Appendix C (lines 6722-6781), and the artifacts `precision-natural-polynomial.json` and
`ordinary-integer-definition.json` (recipes `power_value`, `precision`).

`autoform check blueprint`: OK (173 articles, 439 dependencies). `autoform audit blueprint`:
no finding in my paths. The remaining errors are the coverage rows and the other chapters'
stubs. Commit `0fa1383` is local. **Push failed**: `git push` and `git fetch` to GitHub get
"connection reset by peer" (the writer's report had the same failure), so the branch on GitHub
does not have this commit or the writer's commits `0725810`/`7272fe7`.

## What I fixed

1. **Lowering aliasing bug** (`machine/lowering.md`). In the copy `r:=r'` as written, `r'` was
   emptied into two auxiliaries, then `r` was cleared, then one copy went back to `r'` and one
   into `r`. For `r=r'` that gives `2v`. Now `r'` is restored first, then `r` is cleared and
   filled. I also spelled out the final moves of `∸` and `·` into `r` (through a fresh
   accumulator), and stated the general rule: the destination is written only after all
   sources are copied.
2. **Capped arithmetic at `L=0`** (`machine/capped-arithmetic.md`, `machine/ir-correctness.md`).
   The manuscript states saturation only for positive `L`, and upstream's
   `saturate_pow_saturate` assumes `1 ≤ L`. But `L=⌊(V-1)/(4U)⌋=0` does occur (whenever
   `V-1<4U`). Both articles now treat `L=0` explicitly (both sides false, the program rejects),
   and the note points to `checkedCappedPower_zero_cap`.
3. **Finite check isolated**: new leaf `machine/projective-generator.md` (the fixed Jacobian
   triple `(3282-2320s, -247440+174966s, 4)` lies on `Y²=X³+AXZ⁴` and represents `P_0`). It was
   item 3 of `jacobian-formulas`, which is now generic, with no dependency on `P_0`. I checked
   the triple numerically: both sides equal `122452755912-86587174080 s`. Note: `af_9224e7100caa646cdb5a15d2`.
4. **Missing bound on `c_3`** (new leaf `program-literal-size.md`, plus an upper bound added to
   `machine/program-numbering-decode.md`). Section 12 (line 6374) requires every literal
   constant to be at most `T`, and `c_3` is one of them (`integer_constant_3`). No article
   bounded `c_3` from above. The decoding lemma now states `code(Π)<2^{w(4m+1)+1}`. The new leaf
   (a finite check on the constructed instruction list, never on `c_3`) states that the wrapper
   has `m ≤ 2^20` instructions with all indices below `2^20`, so `5 ≤ c_3 < 2^{83886101} < 2^{2^27}`.
   I calibrated this from the saved literal: `w=18`, about 146,780 instructions, maximum index
   146,779, 10,568,107 bits. Upstream's encoder also picks the least admissible `w`, matching
   `program-numbering`. Note: `af_4a8e044aefac1d6ca7c31346`. New locator anchor
   `#section-12-literal-constants`.
5. `jacobian-formulas`: added the one-line argument that `U_1=U_2` forces `S_1=±S_2`.

## Finite computations in the chapter (after review)

| Leaf | Decidable statement | Size | Method |
| --- | --- | --- | --- |
| `precision-circuit-scope` | power template (474 nodes, 82 vars) and precision circuit (293,620 nodes, 54,056 explicit vars, 15,845 blocks of 79) are well-formed with bounds 82 and 1,305,811; constants `{4,2,3}` and `{c_3,2,4,1399}` | large | item 1 kernel `decide`; item 2 by construction (preferred) or a sound checker with `native_decide` (milestone 1); `c_3 ≥ 2` from its definition, not evaluated |
| `machine/projective-generator` (new) | six explicit integers: curve identity in `ℤ[s]` and coordinates of `P_0` | tiny | `norm_num`/`decide` |
| `program-literal-size` (new) | `length (W Π_prec) ≤ 2^20 ∧ all indices < 2^20` | ~147k instructions | `native_decide` (milestone 1); structural bound on `lower` (milestone 2) |
| (optional, interpreter note) | `U` has 1,399 states and 204 registers | small | `decide` |

I checked these facts against the JSON: 54,051 witnesses plus 5 inputs; blocks pairwise
disjoint, disjoint from the explicit variables, and together with them a partition of
`{0,…,1305810}`; old universal variable count 1,305,804; `power_value` root equality
`[17751579,15]` (value mode, output at reference `15=5·3`); precision root equality `[…,-1]`;
the constant order `c_3→integer_constant_3`, `2→1`, `4→0`, `1399→4`; the pairing nodes match
`Spec(H,e_0)`.

## Verified without change

- Coverage: every claim in lines 5977-6093 has an article or is delegated with a link. The
  `multiply`-internal typing remarks (27 slope calls, 6 test groups) go to the multiplication
  chapter; the signed-encoding and exceptional branches to the assembly chapter; the primitive
  formula compilation to `syntax/sum-of-squares-semantics` and `existential-lifting`.
- Constants: `enc`, `𝒞`, `F`, `A^{(0)}_{ht}=H_6(S_ht;D)` with `S_ht={p≤324}` (line 968) and
  `max(D,317,10^{12})=D`; the threshold `4ε<4^{-B} ⟺ 4^B ≤ ⌊(V-1)/(4U)⌋`; Cantor pairing and the
  four pairing equations; variable shift `i↦i+7`; `V+2=1305806`.
- Jacobian doubling and addition formulas (standard, with `a=A`), and `d²=11243-7950s`.
- Mathlib pointers checked in `.lake/packages/mathlib`: `Nat.sum_four_squares`,
  `QuadraticAlgebra.norm_eq_zero_iff_eq_zero` (needs `Fact (∀ r, r^2 ≠ a + b r)`), Jacobian
  `dblXYZ`/`addXYZ`/`toAffine_add`, `StateTransition.eval`/`mem_eval`/`tr_eval`,
  `Nat.exists_eq_two_pow_mul_odd`, `Nat.digits_ofDigits`, `MvPolynomial.eval₂Hom_bind₁`,
  `Affine.Point.neg_some`, and `QuadraticAlgebra` deriving `DecidableEq`. Upstream names checked
  in `lean/ZInQ`: `CantorDecoder.{pair,loop,decode,encode5,decode5,pairing_equation_iff,…}`,
  `PrecisionArithmetic.saturate_*`, `PrecisionAlgorithms.cappedMul/cappedPower*`,
  `EquationCompression.eval_conjoin_eq_zero_iff`, `CircuitEncoding.Circuit.eval`.
- Dependencies: no cycles. The hypotheses MW and (through the constants of `H_6`) H are
  linked where used. M is taken in its all-input form, which matches Lemma 1.2 ("M on all
  rational input codes").

## Still needs work / open questions

1. **The interpreter generator is not in the repository** (I confirmed the writer's issue 1:
   no `uncons`/`setList` source under `construction/`). The witness budget
   (292,890,231,904, met exactly) depends on reproducing the 1,399-state, 204-register `U`
   exactly. This is a project-level blocker for the natural chapter, not for these
   statements.
2. **Ownership overlap with natural/**: this chapter defines the precision predicate,
   register programs, capped arithmetic, Cantor unpairing and `Spec(H,e_0)`, which come from
   Section 10's opening and 10.1 (the natural chapter's context range). The lead should
   deduplicate. (C.4) itself (`natural/natural-polynomial-semantics.md`) must be proved from
   the natural chapter's packed-compiler theorem for `U` plus `machine/specialization-semantics`
   and `machine/precision-machine-semantics`. Those edges are not in the graph yet.
3. `precision-circuit-scope`, `rational-translation` and `syntax/recipes/*` use
   `natural-polynomial-semantics` (a theorem) as their statement dependency for the
   *definition* of `C` and its circuit. Once the natural chapter has a `def` article for the
   circuit, these links should point to it.
4. Injectivity of `ι` is cited from the generator certificate (MW). It needs only infinite
   order of `P_0`, which follows from the torsion theorem without MW (see
   `machine/nondegenerate-multiples`). This is harmless because M needs MW anyway, but the
   writer's remark that "the rational translation depends on the rational model" holds through
   M, not through injectivity.
5. Size chapter: it must use `program-literal-size` for `c_3 ≤ T`; `T ≥ D` with
   `log₂ D > 256·(324!)^4 > 2^27` closes it symbolically.

## Faithfulness verdict

The chapter is faithful to Sections 10.3-10.4. Each statement matches the manuscript's
constants, domains (ℕ for natural witnesses and inputs, ℤ for indices and node values, ℚ⁵ for
codes) and quantifier structure. The rational translation is stated in the exact two-sided,
all-input form that input C needs: arbitrary rational tuples on the precision side, canonical
inputs only for `power_value`. Where the manuscript is terse or slightly off, the writer's
expansions are correct and recorded: the nondegeneracy needed for `z=-x/y`; that both index
witnesses of `multiply(σ,σ,Σ)` coincide; that nontrivial constants are positive; that
`A^{(0)}_{ht}` is taken at `R=D`. After this review three more gaps are closed: a lowering
aliasing error, the `L=0` case of capped arithmetic, and the missing upper bound on `c_3`
needed by Section 12. One isolated finite check was also added. What remains is outside these
statements: reproducing the archived interpreter exactly, and wiring (C.4) in the natural
chapter.
