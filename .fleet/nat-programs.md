# nat-programs: report

Programs of the natural compiler (`blueprint/roadmap/compiler/natural/programs/`). All code is
in `ZInQKernel/Compiler/Programs/` (namespace `ZInQ.Compiler.IR`), root module
`ZInQKernel/Compiler/Programs.lean`. `lake build ZInQKernel` succeeds. No `sorry`, no
`axiom`, no `native_decide`. The main theorems depend only on `propext`, `Classical.choice`,
`Quot.sound`. The finite checks are `decide +kernel` on structural counts (see below).

## Leaves

| Article | Lean name(s) | Status |
| --- | --- | --- |
| programs/structured-programs.md | `Op`, `Stmt`, `Outcome`, `BigStep`, `BigStep.deterministic`, `Program`, `Program.WF`, `Program.Accepts`, `Program.Total` (`IR.lean`) | proved |
| programs/lowering.md | `assignB`, `ltTest`, `eqTest`, `code`, `Stmt.len`, `code_length`, `cleanup`, `lower`, `lower_length` (`Lowering.lean`); `lower_valid` (`LoweringValid.lean`) | proved |
| programs/lowering-correct.md | `code_forward`, `code_backward` (item 0), `lower_accepts_of_accepts` (item 1), `accepts_of_lower_halts` (item 2), `lower_halts_iff`, `lower_accepts_iff`, `lowering_correct`, `lower_not_halts_of_reject` (`LoweringCorrect.lean`); block lemmas in `Blocks.lean` | proved |
| programs/cantor-pairing.md | upstream `ZInQ.CantorDecoder.pair`, `loop`, `decode`, `encode5`, `decode5`; tuple form `dec5` (`WrapperCorrect.lean`) | proved (definitions upstream) |
| programs/cantor-unpairing.md | `cantor_pair_props` (1), `cantor_unpair_props` (2), `cantor_pairing_equation` (3), `pairing_system_iff`, `pairing_system_encode` (4) (`Cantor.lean`) | proved |
| programs/ir-integer-routines.md | `SInt`, `ReprInt`, `sDecode`, `sConst`, `sCopy`, `sNeg`, `sAbs`, `sAdd`, `sSub`, `sMul`, `sDiv`, `sMod`, `nOp`, `sLtFlag`, `sEqFlag` (`Signed.lean`); `SContract`, `*_spec` (`SignedSpec.lean`) | proved |
| programs/ir-field-routines.md | `FExpr`, `FExpr.code`, `FExpr.assign`, `fMul`, `IExpr`, `zeroFlag`, `guardNonzero`, `natConst`, `intConst` (`Field.lean`); `fMul_spec`, `FExpr.code_spec`, `FExpr.assign_spec`, `IExpr.code_spec`, `zeroFlag_spec`, `guardNonzero_spec`, `intConst_spec` (`FieldSpec.lean`) | proved |
| programs/ir-point-routines.md | `ptOf`, `copyPt`, `setO`, `setP0`, `jdblCode`, `jdblBCode`, `jaddBCode`, `jmulCode` (`Point.lean`); `jdblCode_spec`, `jdblBCode_spec`, `jaddBCode_spec`, `jmulLoop_spec`, `jmulCode_spec` (`PointSpec.lean`) | proved |
| programs/ir-capped-routines.md | `satCode`, `cmulCode`, `cpowCode`, `cfactCode`, `caddCode`, `cmaxCode`, `satLit`, `cA0Code`, `cBoundCode`, `divFourCode` (`Capped.lean`); the matching `*_spec` (`CappedSpec.lean`), e.g. `cA0Code_spec : … = NExpr.eA.capped L`, `cBoundCode_spec : … = cappedBound L M` | proved |
| programs/precision-ir.md | `precisionZ` (integer program), `precisionProgram` (`PrecisionIR.lean`), `precisionProgram_wf` | proved |
| programs/precision-ir-correct.md | `precisionZ_spec`, `precisionProgram_bigStep`, `precisionProgram_total`, `precisionProgram_correct` (↔ `decide5 c = true`), `precisionProgram_accepts_iff` (↔ `accepts c`), `precisionProgram_reject_of_not_early` (`PrecisionCorrect.lean`) | proved |
| programs/wrapper-program.md | `unpairStep`, `unpairBody`, `unpairProgram`, `wrapperPrefix`, `relocate`, `wrapper` (`Wrapper.lean`); `wrapper_valid` (valid for `r_prec + 10`), `wrapper_size` (`WrapperValid.lean`) | proved |
| programs/wrapper-correct.md | `wrapper_prefix_reaches`, `stepN_shift`, `wrapper_halts_iff_machine`, `wrapper_halts_iff` (↔ `accepts (dec5 x)`), `wrapper_halts_encode` (↔ `accepts c`) (`WrapperCorrect.lean`) | proved |
| programs/precision-machine.md | `precisionMachine`, `precRegs`, `precisionMachine_halts_iff`, `precisionMachine_accepts_iff`, `precisionMachine_correct`, `precisionMachine_not_halts`, `precisionMachine_valid` | proved |

For nat-halting: the program literal is `ZInQ.Compiler.IR.wrapper : RM.Program`, with
`wrapper_halts_encode`, `wrapper_valid : wrapper.Valid (precRegs + 10)` and `wrapper_size :
3 ≤ wrapper.length ∧ wrapper.length ≤ 200000 ∧ precRegs + 10 ≤ 2 ^ 18`. Currently
`wrapper.length = 133092` and `precRegs = 828`. The definition changed slightly after the first
commit (`satCode` reads its operand as `x · 1`; the exponent `24` of `β` is an exact constant).
Only the name `wrapper` should be relied on, never its digits.

## Statement corrections and design choices

- structured-programs: `Program` has explicit fields `body`, `bound`, `inputs`; the article's
  side conditions (registers below the bound, `k ≤ bound`) are `Program.WF`.
- lowering: the six auxiliary registers `J + 1, …, J + 6` are shared by all blocks (each block
  starts and ends with them zero, the article's "or registers it clears before use"), so the
  register count is `r = J + 7`. A test does not store the comparison in a flag register; the
  comparison loop branches directly to the two targets. The layout is: open code at `0`, the
  self-loop at `n = S.len` (the normal exit and the `reject` target), cleanup from `n + 1`
  (`dec i` self-loops for `i < r`), the final halt at `n + r + 1`. A constant `x ← k` costs
  `k + 1` instructions, so programs build large constants by Horner's rule (`natConst`).
- lowering-correct, item 0 backward: the formal statement is `code_backward`: if the run from
  the entry reaches a halting state after `t` steps, then `⟨S', ρ⟩ ⇓ accept`, or
  `⟨S', ρ⟩ ⇓ normal ρ'` and the run from the normal exit halts after at most `t` steps, or
  `⟨S', ρ⟩ ⇓ reject` and the run from the reject target halts. This gives item 2 because the
  self-loop never halts.
- integer routines: the temporaries are all the registers from the base `t` on (the frame
  condition is "every register below `t` other than the result pair is unchanged"). Results
  may alias operands. `div`/`mod` act on absolute values. "Multiplication by a constant" and
  "multiplication of two naturals into a signed result" are not separate routines (constant
  plus `sMul`, or `nOp`). The tests `z₁ < z₂` and `z₁ = z₂` compute a flag (`sLtFlag`,
  `sEqFlag`), and the branch is taken by the integer layer. Zero tests are done there on
  absolute values.
- New intermediate layer (not in the blueprint): the routines and the precision program are
  written in an integer language `ZStmt` (`ZL.lean`), with assignments over integer variables,
  absolute-value tests `nlt`/`neq`, signed tests `lt`/`eq`, and loops `while |a| < |b|`. It has
  a big-step semantics on environments `ℕ → ℤ` and a compiler to the ideal register language
  (variable `k` ↦ signed pair `(off + 2k, off + 2k + 1)`). `ZStmt.compile_sim` (`ZLSim.lean`)
  proves the simulation once, so the field, point and capped routines and the precision program
  are verified on integers.
- field routines: provided as an expression compiler (`FExpr`: pair variables, integer
  variables, constants, `+`, `-`, `·`, negation, conjugation) instead of separately named
  routines. The norm is the integer expression `normI`. The comparison of two rationals
  `θ₁/δ₁ < θ₂/δ₂` is not implemented: the decision program needs only the integer closeness
  inequality `|θ - nδ| V < U |δ|`, which is computed directly.
- capped routines: the capped power is computed by `e` capped multiplications, not by
  binary exponentiation. Its value is the same, `cpow_L(x, e) = σ_L(x^e)` (upstream
  `cappedPower_eq_saturate`), and the cost does not matter in the ideal semantics. `⟨e_A⟩_L` is
  computed by a straight-line capped program with the shared subexpressions `F₀`, `D`, `D²`,
  computed once (`cA0List`), and proved equal to `NExpr.eA.capped L` by unfolding, never by
  evaluation.
- precision-ir: the early test `n ∉ 𝒞` is computed as `F(n) ≠ 0` (`sixF_eq_zero_iff`), and
  `F(n)` is reused for `M`. The three scalar multiplications run in one loop over a counter,
  with one copy of the halving code; this keeps the wrapper at 133,092 instructions.
- wrapper-program: the prefix's working registers are `r_prec, r_prec + 1, r_prec + 2`, its
  jump register is `r_prec + 3` and its auxiliary registers are `r_prec + 4, …, r_prec + 9`.
  `𝒲` is valid for `r_prec + 10` registers.
- cantor-unpairing item 4 is stated with `tNext` (`t₄ = c₄`), as an iff with the four
  equations `tᵢ = pair(cᵢ, tᵢ₊₁)`, plus `pairing_system_encode` for `t₀ = enc₅(c)`.

## Lemmas added beyond the leaves

- RM runs: `Reaches`, `ReachesIn`, `halts_after` (determinism of halting runs), `Embedded`,
  `reaches_clear`, `reaches_transfer1/2` (`Runs.lean`), and the block lemmas `Embedded.snap`,
  `reaches_monus`, `reaches_mulLoop`, `reaches_divLoop`, `reaches_ltLoop`, `reaches_eqLoop`,
  `assignB_reaches`, `ltTest_reaches`, `eqTest_reaches` (`Blocks.lean`).
- Loop-free executors: `Stmt.execF`/`bigStep_execF` and `ZStmt.execZ`/`zbigStep_execZ`, the
  latter with Boolean tests (`ZCond.btest`).
- Straight-line program abstractions with functional semantics: `FProg` (pairs), `CProg`
  (capped operations), `SLProg` (integer and pair assignments), `guardsCode`.
- Structural bounds: `ZStmt.varsBound`, `Stmt.regsBound` with soundness lemmas. Kernel checks
  (`decide +kernel`, fast): `precisionZ_varsBound`, `precisionProgram_regsBound`,
  `unpairProgram_regsBound`, `five_le_precRegs`, `wrapper_size`.

## Problems met

- `simp` cannot rewrite inside an `if` condition when the `Decidable` instance still mentions
  the term before rewriting (this happens after `Function.update` chains). The executors
  therefore use Boolean tests (`Nat.blt`, `Nat.beq`, `zblt`, `zbeq`) and turn them into
  propositions only at the end. The routines are also arranged so that no condition reads a
  register written earlier in the same routine.
- Closed terms such as `wrapper.length`, `precisionMachine.length` and `precRegs` must never
  meet `omega`, `simp` closing by `rfl`, `show` or `decide` in the elaborator: definitional
  unfolding evaluates the 133k-instruction list (kernel checks of 2 minutes, or recursion
  limits). Generalize them first, or argue through `lower_length`/`code_length`.
- `omega` does not unfold the abbreviation `aux`; use `simp only [aux]` first (macro `aomega`).

## Suggestions

- universal/wrapper-size-check: `wrapper_valid` and `wrapper_size` give it directly. Every
  register index is below `precRegs + 10 ≤ 2^18`, and every target is below
  `wrapper.length ≤ 200000 < 2^18`. Only the `maxField` packaging remains.
- If the interpreter task wants to reuse the lowering blocks, note that their exact shapes
  differ from upstream's recovered interpreter (the copy block here snapshots through `A₀`,
  `A₁`). The generic `reaches_transfer*`/`reaches_clear` lemmas still apply.
- The wrapper could be made smaller by sharing the two copies of `jdbl`. It is not needed:
  133,092 ≤ 200,000.
