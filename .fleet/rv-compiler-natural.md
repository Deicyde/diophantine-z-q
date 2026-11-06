# rv-compiler-natural: adversarial review report

Reviewed: `blueprint/roadmap/compiler/natural/` (README, 6 subchapters, 85 leaves after
review), their implementation notes, and `blueprint/sources/compiler-natural-locators.md`.
I checked them against manuscript lines 5745-6050 (Section 10 opening, 10.1, 10.2, and 10.3,
which the chapter also needs because (C.4) is stated at its end), the Section 4 constants
(lines 377-399, 968-971), Section 12 (lines 6373-6376), the construction notes
(`integer-compiler-spec.txt`, `integer-halting-correctness-proof.txt`), the JS compiler, the
saved `precision-natural-polynomial.json`, and the upstream `lean/ZInQ` helpers.

**Process notes.** The writer's summary `.fleet/bp-compiler-natural.md` is not in the
worktree; the writer's only commit is `4480436` (chapter, no report). `git fetch` and
`git push` both fail with "Recv failure: Connection reset by peer" (the same failure the
other reviewers reported), so I could not see whether anything newer is on GitHub, and my
commits are local only (see the end of this report).

`autoform check blueprint`: OK (226 articles, 547 dependencies). `autoform audit blueprint`:
no finding in my paths. The remaining errors are the coverage rows (`declared-coverage-gap`)
and other chapters' interface stubs (`missing-source-link`).

## What I verified independently

- **Saved polynomial (shape cross-check only).** 54,056 explicit variables (5 inputs, 4
  pairing, 54,047 shifted), 15,845 blocks of 79, variable count 1,305,811; 293,620 nodes =
  54,056 var + 10 const + 125,327 add + 98,382 mul + 15,845 call; constants
  `c3, 0, 1, 2, 4, 1399, -1, 1, 2, -1`, with `c3` at node 0 (3,181,317 digits); the 52
  appended nodes match `precision-circuit` exactly (vars 0-4, 6, 7, 8; consts 1, 2, -1; four
  8-node pairing polynomials; 9-node sum of squares, root 293619); the power template has
  474 nodes (82/6/196/190) with constants `0,1,4,2,3,-1`; first blocks start at 1824 and 1904,
  consistent with the counter semantics of hierarchical calls.
- **Counting formula.** `2k+9+41r+10m+31s` explicit variables and `2+3(m+4r+3s)` calls,
  re-derived from `compileRegisterMachine`. With k=2, r=204, m=1399, s=1022 they give 54,049
  and 15,845, so 1,305,804 variables. The JSON's variable-name counts agree
  (`strict_difference` 10,770, `binomial_*` 5,281, `orthogonal_binomial` 3,678,
  `mask_binomial` 1,603, `and_left_only` 1,226, `sub_nonzero_` 1,022).
- **Interpreter recovery.** I parsed the state equations `S_d = [d=0] + B·I_d` from the
  JSON: 1,399 states, 1,022 sub instructions, cleanup `dec(j,1194+j,1195+j)` for j<204,
  halt at 1398, and the only states below 1194 that jump into cleanup are 69, 587 and 593
  (each `dec(2,1194,1194)`). This confirms the writer's note.
- **Jacobian identities (sympy).** `E(dbl P) ∈ (E(P))` and
  `E(add P1 P2) ∈ (E(P1), E(P2))`: the remainders on division in `Y`, `Y1`, `Y2` vanish
  identically, so cofactors over ℤ exist. The fixed triple satisfies the curve equation;
  both sides equal `122452755912 − 86587174080·√2`.
- **Mathematics re-derived by hand:** every step of the alpha articles (growth, matrix,
  Pell descent for every `b` in the ordered case, (C.1), folding, period and reflection,
  the companion bound, soundness and completeness of (C.2)); the power formula (C.3),
  including `E_{R+1} − Q E_R = m U_R` and `m > Q^R`; the binomial digit; Lucas; AND; the
  packed decoding (digit bounds ≤ K < B, the extra slot q+1, q = 0); Cantor unpairing;
  program-code bounds; the precision threshold; saturation; the decision-program algebra
  (`z = −XZ/Y`, `ε_l = (|p|+|p'|)/|N_l|`, `r = θ/δ`, the cross-multiplied closeness test).
- **Names in notes.** I checked every upstream name the notes cite against
  `lean/ZInQ/*.lean`; all exist. I checked every Mathlib/core name with one
  `lake env lean` `#check` run (load about 7, 118 GB free). Three did not exist and are
  fixed: `MvPolynomial.eval_bind₁` → `aeval_bind₁`/`eval₂Hom_bind₁`,
  `Zsqrtd.star_re` → `Zsqrtd.re_star`, and `List.sum_map_count`, which I replaced with
  `List.countP_append`. `PackedRegister.digits_eq_of_sum_eq` is `private`, and `lean/`
  stays unchanged; the notes now say to reprove it.

## What I fixed

1. **Bound on the program literal was too weak for its consumer** (`universal/wrapper-code-size.md`).
   It claimed `c_3 < 2^20000000`, citing a size-chapter requirement of "fewer than
   20,000,000 binary digits" that exists nowhere. The size chapter actually uses
   `|c_3| < 2^{2^24}`, and `2^24 = 16,777,216 < 20,000,000`; the old route gave only
   `2^18874387`. New statement: `1399 < c_3 < 2^14400019 < 2^{2^24}`, from a finite check
   with a tighter instruction bound (see 2).
2. **Finite checks isolated** (I split the universal subchapter):
   - new `universal/wrapper-size-check.md`: `3 ≤ m_W ≤ 200,000` and every register index
     and target of `W` is below `2^18`. This is a requirement on the freshly written
     wrapper. The manuscript's wrapper (146,780 instructions, 23,633 registers) meets it.
   - `universal/interpreter-shape.md` is now only the decidable shape: validity for 204
     registers, 1,399/1,022/376, and the cleanup structure with predecessors 69, 587, 593.
     The correctness proof used that structure, but it had been left in a note.
   - new `universal/halting-circuit-counts.md`: 54,049 / 15,845 / 1,305,804 / macro counts
     and well-scopedness of `H`, derived from the shape and the counting lemma. These
     counts used to be asserted inside the definition `halting-polynomial.md`.
   - new `universal/halting-node-check.md`: node statistics of `H` (293,568 nodes) and of
     the power template (474 nodes). These used to be bundled with a derived item and
     asserted inside the definition `power-template.md`.
   - `universal/circuit-node-counts.md` is now "Shape of the natural precision circuit",
     derived from those checks. It used to be asserted in the definition `precision-circuit.md`.
   - new `precision/jacobian-generator.md`: the fixed Jacobian point is `P_0`, a closed
     identity on six integers. It used to be item 9 of the generic `jacobian-formulas.md`,
     which no longer depends on `P_0`.
3. **Capped constant made precise** (`precision/capped-height-test.md`). The article wrote
   `⟨D⟩`, then "and likewise `⟨E_0⟩`, ..., `⟨C_cm⟩`". It now defines the capped value
   `⟨e⟩_L` of any expression built from literals, +, ·, max, powers and factorials, and the
   expression `e_A` with every literal shown. It proves `⟨e⟩_L = σ_L([[e]])` by induction,
   including the factorial case `f_L(σ_L(n)) = σ_L(n!)` that was missing. The definitions of
   `decision-program` and `ir-capped-routines` now use `cmul_L(⟨e_A⟩_L, cpow_L(σ_L(M),24))`.
4. **Lowering block order** (`programs/lowering.md`). The text was ambiguous about when the
   destination is cleared. It now says: snapshot every source (move into two auxiliaries,
   restore from one), and only then clear and write `x`. Each block (∸, ·, div, mod and the
   zero-divisor case) is spelled out. This is the aliasing bug the compiler-translation
   reviewer found in their duplicate of this article; ours left it unspecified.
5. **Well-scopedness of `N` stated** (`universal/precision-circuit-specialization.md`). Section
   10.4 (lines 6082-6085) uses "no parent variable node accesses a private coordinate". It is
   now an explicit claim with a proof via the counts of `H` and injectivity of the shift.
6. `natural-polynomial-semantics.md`: depends in its proof on the shape of `N`, which gives
   the exponent 1,305,806. A sentence now points to the admissibility bridge
   (`precision/precision-guards.md`), so consumers see why the relation contains
   admissibility.
7. README: replaced the unsupported "about 1.7 million power calls" with the provable lower
   bound `2+3(146,780+4·23,633) = 723,938`.
8. Small fixes: overloaded `mul(k)` notation (scalar multiplication); the interpreter
   correctness proof now cites the shape check; notes updated (`packed-transitions` wrongly
   called item 2 an instance of item 1; the private upstream lemma; `capped-height-test`,
   `decision-program` and `ir-capped-routines` renamed to `NExpr.capped`/`eA.capped`;
   `precision-ir` size target); new locator anchor `#section-12-literal-constants`.

## Articles (85 leaves; new in this review: halting-circuit-counts, halting-node-check, wrapper-size-check, jacobian-generator)

| Path | Kind | Title |
| --- | --- | --- |
| `exponential/alpha-divisibility.md` | theorem, cited | Divisibility of alpha values |
| `exponential/alpha-equations-complete.md` | theorem, cited | Completeness of the alpha formula |
| `exponential/alpha-equations.md` | def, cited | The alpha formula |
| `exponential/alpha-equations-sound.md` | theorem, cited | Soundness of the alpha formula |
| `exponential/alpha-growth.md` | theorem, cited | Growth of the alpha sequence |
| `exponential/alpha-large-odd.md` | theorem, cited | Odd alpha values are unbounded |
| `exponential/alpha-matrix.md` | theorem, cited | Matrix powers and the quadratic identity |
| `exponential/alpha-parameter-congruence.md` | theorem, cited | Parameter congruence of the alpha sequence |
| `exponential/alpha-pell.md` | theorem, cited | Natural solutions of the alpha Pell equation |
| `exponential/alpha-period.md` | theorem, cited | Period and reflection modulo the companion |
| `exponential/alpha-sequence.md` | def, background | The alpha sequence |
| `exponential/binomial-digit.md` | theorem, cited | Binomial coefficients as base-B digits |
| `exponential/bit-and.md` | theorem, cited | The bitwise AND gadget |
| `exponential/lucas-bits.md` | theorem, background | Lucas's criterion for bit inclusion and disjointness |
| `exponential/power-equations-correct.md` | theorem, cited | The power formula expresses exponentiation |
| `exponential/power-equations.md` | def, cited | The power formula |
| `formulas/hierarchical-calls.md` | theorem, cited | Circuits of hierarchical constructions |
| `formulas/macro-semantics.md` | theorem, bridged | Semantics of the natural macros |
| `formulas/natural-atom-gadgets.md` | theorem, cited | The equational gadgets over the naturals |
| `formulas/natural-circuit-semantics.md` | def, bridged | Natural semantics of a natural circuit |
| `formulas/natural-compilation.md` | theorem, cited | Compilation and private witnesses over the naturals |
| `formulas/natural-constructions.md` | def, cited | Natural constructions and their macros |
| `formulas/power-template.md` | def, cited | The power template |
| `formulas/power-template-semantics.md` | theorem, cited | Semantics of the power template |
| `natural-polynomial-semantics.md` | theorem, cited | Semantics of the natural precision polynomial |
| `packed/packed-branches.md` | theorem, cited | Branch histories and indicator digits |
| `packed/packed-compiler.md` | def, cited | The packed-history construction |
| `packed/packed-complete.md` | theorem, cited | Completeness of the packed-history construction |
| `packed/packed-counts.md` | theorem, bridged | Variable and gadget counts of the packed construction |
| `packed/packed-masks.md` | theorem, cited | Digits of masked histories |
| `packed/packed-nonzero-indicator.md` | theorem, cited | The packed nonzero indicator |
| `packed/packed-sound.md` | theorem, cited | Soundness of the packed-history construction |
| `packed/packed-state-selection.md` | theorem, cited | One active state per time slot |
| `packed/packed-transitions.md` | theorem, cited | Decoding the transition equations |
| `packed/register-machine-polynomial.md` | theorem, cited | The compiled circuit of a register machine |
| `precision/capped-height-test.md` | theorem, bridged | The capped precision test |
| `precision/capped-power.md` | theorem, cited | Capped multiplication and binary exponentiation |
| `precision/decision-program-correct.md` | theorem, cited | Correctness of the decision program |
| `precision/decision-program.md` | def, cited | The exact decision program |
| `precision/jacobian-formulas.md` | theorem, cited | Jacobian formulas on the weighted model |
| `precision/jacobian-generator.md` | theorem, cited | The fixed Jacobian point |
| `precision/jacobian-scalar-multiplication.md` | theorem, cited | Scalar multiplication by halving |
| `precision/norm-zero.md` | theorem, cited | Elements of norm zero |
| `precision/precision-guards.md` | theorem, bridged | Admissibility of nonzero indices |
| `precision/precision-height-constant.md` | def, cited | The precision height constant |
| `precision/precision-height-constant-value.md` | theorem, bridged | The precision constant is the six-contact constant |
| `precision/precision-relation.md` | def, cited | The precision relation |
| `precision/precision-threshold.md` | theorem, cited | The precision threshold as an integer comparison |
| `precision/saturated-arithmetic.md` | theorem, cited | Saturated arithmetic |
| `precision/signed-encoding-bijection.md` | theorem, bridged | The signed encoding is a bijection |
| `precision/signed-encoding.md` | def, cited | The signed encoding of integers |
| `precision/z-coordinate.md` | def, cited | The local parameter z on multiples of the generator |
| `programs/cantor-pairing.md` | def, cited | Cantor pairing and its decoder |
| `programs/cantor-unpairing.md` | theorem, cited | Unique Cantor unpairing |
| `programs/ir-capped-routines.md` | theorem, cited | Capped arithmetic routines |
| `programs/ir-field-routines.md` | theorem, cited | Quadratic-field routines |
| `programs/ir-integer-routines.md` | theorem, cited | Signed integer routines |
| `programs/ir-point-routines.md` | theorem, cited | Point routines |
| `programs/lowering-correct.md` | theorem, cited | Correctness of the lowering |
| `programs/lowering.md` | def, cited | Lowering to primitive programs |
| `programs/precision-ir-correct.md` | theorem, cited | Correctness of the precision program |
| `programs/precision-ir.md` | def, cited | The precision program |
| `programs/precision-machine.md` | theorem, cited | The precision machine halts exactly on acceptance |
| `programs/register-machine.md` | def, cited | Register machines |
| `programs/structured-programs.md` | def, cited | The ideal register language |
| `programs/wrapper-correct.md` | theorem, cited | Correctness of the wrapper |
| `programs/wrapper-program.md` | def, cited | The wrapper program |
| `universal/circuit-node-counts.md` | theorem, cited | Shape of the natural precision circuit |
| `universal/halting-circuit-counts.md` | theorem, cited | Counts of the universal halting circuit |
| `universal/halting-node-check.md` | theorem, cited | Node statistics of the halting circuit and the power template |
| `universal/halting-polynomial.md` | def, cited | The universal halting circuit |
| `universal/halting-polynomial-semantics.md` | theorem, cited | Semantics of the universal halting circuit |
| `universal/interpreter-correct.md` | theorem, cited | Correctness of the universal interpreter |
| `universal/interpreter-list-primitives.md` | theorem, cited | List blocks of the interpreter |
| `universal/interpreter-primitives.md` | theorem, cited | Arithmetic blocks of the interpreter |
| `universal/interpreter-shape.md` | theorem, cited | Shape of the universal interpreter |
| `universal/interpreter-step.md` | theorem, cited | One interpreter loop simulates one instruction |
| `universal/precision-circuit.md` | def, cited | The five-input natural precision circuit |
| `universal/precision-circuit-specialization.md` | theorem, cited | The precision circuit is a specialization |
| `universal/program-numbering-encode.md` | theorem, bridged | Codes of primitive programs |
| `universal/program-numbering.md` | def, cited | The universal program numbering |
| `universal/tape-lists.md` | theorem, cited | Tape lists |
| `universal/universal-interpreter.md` | def, cited | The universal interpreter |
| `universal/wrapper-code-size.md` | theorem, bridged | Size of the program literal |
| `universal/wrapper-size-check.md` | theorem, bridged | Size of the wrapper |

## Finite computations (after review)

| Leaf | Decidable statement | Size | Method |
| --- | --- | --- | --- |
| `universal/interpreter-shape` | `U.Valid 204 ∧ len = 1399 ∧ subCount = 1022 ∧ addCount = 376 ∧` cleanup `dec j (1194+j) (1195+j)` ∧ `U[1398] = halt` ∧ predecessors of cleanup below 1194 are `[69,587,593]`, each `dec 2 1194 1194` | 1,399 small instructions | kernel `decide` (or a Boolean checker closed by `rfl`) |
| `universal/halting-node-check` | `H` has 293,568 nodes (54,049 var, consts `[0,1,2,4,1399,-1]`, 125,307 add, 98,361 mul, 15,845 call; nodes 0, 1 are `var 0`, `var 1`); power template has 474 nodes (82/`[0,1,4,2,3,-1]`/196/190/0) | 293,568 hash-consed nodes; 474 | power template: `decide`. `H`: `native_decide` at milestone 1; at milestone 2 a kernel Boolean checker with a `Nat`-keyed trie, or a symbolic sharing analysis. Exact counts are needed by the variable budget |
| `universal/wrapper-size-check` | `3 ≤ W.length ≤ 200000 ∧ ∀ ins ∈ W, ins.maxField < 2^18` | ~1.5·10^5 instructions | structural size functions `IR.size`, `IR.maxReg` evaluated by `decide` on the IR term; `native_decide` at milestone 1 |
| `precision/jacobian-generator` | `Y0² = X0³ + A·X0·Z0⁴` in `ℤ√2`, plus the two affine quotients equal `P_0` | 12-digit integers | `decide`/`norm_num` |
| inline in `precision/precision-height-constant-value` | `10^12 < 20!` (with `20! ≤ 324!` by monotonicity) | 19 digits | `norm_num`. Left inline on purpose: a single numeral comparison |

No finite computation touches `c_3`, `D`, `Q_0`, `B_cm`, `C_cm` or `A^{(0)}_ht`.

## Extra hypotheses

None beyond the five. Equation (C.4) uses no hypothesis. The precision relation includes
admissibility of `l, a, j` (`[k]P_0` affine with nonzero ordinate). This makes the
relation and its computation independent of the generator theorem.
`precision/precision-guards.md` (hypothesis: `P_0` has infinite order, which the model
chapter's generator theorem supplies under Mordell–Weil) proves that admissibility follows
from the early tests. Only the assembly side needs that.

## Manuscript issues (writer's and mine)

1. The manuscript defines `z` only on nonzero multiples of `P_0`, but its program is total
   and rejects degenerate points. The relation is stated with an explicit admissibility
   clause, which is equivalent given the generator theorem.
2. The "nine exact polynomial identities" are not listed. The chapter fixes its own list:
   8 generic items plus the fixed-point check.
3. The growth inequalities hold for `b ≥ 2`, not only `b ≥ 3`. This is a stated
   strengthening, true and harmless.
4. S21, S22, S23 and the interpreter source are not in the repository. The decision program,
   IR, lowering and wrapper are specified afresh, so the Lean `c_3` will differ from the
   saved literal. The universal interpreter must be reproduced exactly, because the
   variable budget has no slack; it can be recovered from the saved circuit, as confirmed
   above.
5. (Review) The manuscript fixes no bound on `c_3` beyond "≤ T" (Section 12, lines
   6373-6376). Downstream chapters quote the saved literal's 3,181,317 digits, which do not
   apply to the Lean literal.

## Cross-chapter issues for the lead (not in my paths)

- **Duplication with `compiler/translation/machine/`** (branch `wip/bp-compiler-translation`,
  23 leaves). It redefines the precision predicate, register programs, numbering,
  interpreter, interpreter step, lowering, structured programs, IR, Jacobian formulas, norm
  zero, capped arithmetic, Cantor unpairing, wrapper, specialization and the precision
  machine. All of these are in this chapter, which owns (C.4). That subchapter should link
  `compiler/natural/*` instead. Its `program-literal-size` uses a different bound
  (`m ≤ 2^20`, `c_3 < 2^{2^27}`); one statement should survive. Ours is
  `universal/wrapper-code-size.md` with `c_3 < 2^{2^24}`.
- **Syntax chapter** `syntax/recipes/natural-circuit-statistics.md` restates the shape of `N`
  and depends on `natural-polynomial-semantics`. It should depend on
  `compiler/natural/universal/precision-circuit.md` and take its proof from
  `compiler/natural/universal/circuit-node-counts.md`. Ideally both resolve to one Lean
  declaration, `precisionCircuit_shape`.
- **Size chapter** (`size/majorants/admissible-cutoff.md`,
  `size/constants/closed-comparisons.md` on `wip/bp-size`) derives `|c_3| < 2^{2^24}` from the
  saved literal's digit count. It should cite `universal/wrapper-code-size.md` instead.
- **Assembly** `assembly/approximation/close-relation.md` and compiler-translation's
  `precision-decision.md` restate the precision predicate. Both should use
  `precision/precision-relation.md` (via `natural-polynomial-semantics`) together with
  `precision/precision-guards.md`.

## Still open

- The interpreter must reproduce the recovered 1,399-instruction program exactly. The
  plan is a structured assembly checked equal to the literal by `decide`, and the
  reverse-engineering of the block shapes is real work (`universal-interpreter` note).
- The node-statistics check on `H` has no kernel route yet: only `native_decide`, or a
  symbolic sharing analysis still to be designed.
- The wrapper size bound is a design constraint on the IR program, which is not yet
  written.
- `lowering-correct` (about 400 lines) and `packed-sound` (about 300 lines) are at the upper
  end of PR size; their notes suggest splitting by block family.
- The AFP correspondence (`alpha_equations`, `exp_repr`) is stated from the construction
  notes. I could not re-check it against the AFP source offline; the Lean proofs do not
  depend on it.

## Faithfulness verdict

The chapter is faithful to Sections 10, 10.1 and 10.2, and to the part of 10.3 needed for
(C.4). Every constant, count and formula I checked matches the manuscript and the saved
artifacts. That covers (C.1)–(C.3), the fifteen alpha conditions, the power branches, the
packed-history equations, the pairing equations and the 1,305,811/54,056/15,845/293,620
shape. The quantifiers and strictness are also right: both precision tests strict, natural
witnesses only, `b > 3`, `m > 0`, `k > 0`. Every proof sketch I re-derived is sound and
detailed enough for a formalizer. Where the manuscript calls a step clear, the chapter
expands it: the sign bookkeeping in folding, the zero-modulus congruence, the q+1 slot,
`q = 0`, and capping with base 0 and 1. There are two deliberate, documented deviations:
admissibility is explicit in the precision relation, and the precision program, lowering
and wrapper are specified afresh because S21–S23 are absent. Neither changes (C.4) given
the generator theorem. The substantive defects I found were a bound on `c_3` too weak for
its consumer, finite checks bundled into derived statements and definitions, an
underspecified capped-constant evaluation and an ambiguous lowering-block order. All are
fixed. The biggest remaining risks are engineering, not mathematics: exact reproduction of
the universal interpreter, and a kernel route for the 293,568-node statistics.

## Push status

The commits `a101494` (review fixes) and the commit adding this report are local on
`wip/bp-compiler-natural` in `~/dzq-wt/bp-compiler-natural`. Three push attempts and
`git ls-remote` all failed with "Recv failure: Connection reset by peer". Run
`git push origin HEAD:wip/bp-compiler-natural` from that worktree once GitHub is reachable.
