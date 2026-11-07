# Blueprint audit of compiler/natural (task bp-audit-natural)

Scope: the 85 articles under `blueprint/roadmap/compiler/natural/` (all subdirectories) whose
frontmatter has `statement: formalized`, audited at commit `de90139`. For each article I
compared the statement (the text before **Proof sketch.** or the first `##` heading) with the
Lean declarations in its `lean:` field.

The previous Lean audit (`lean-audit-2026-11-06.md`, at `0bea4dc`) covered only
`natural-polynomial-semantics.md` in this directory. Since then that article changed only in
its frontmatter, but `Compiler/Universal/WrapperCode.lean` changed, so I re-audited it. Its
verdict is still faithful.

Checks run:
- `lake build ZInQKernel` succeeds; the only `sorry` warning is `Main.lean:34`.
- `autoform check blueprint --lean-root .` passes before and after the edits: 353 articles,
  897 names resolved.
- A scratch file `#check`ed every unlisted name recommended below. All exist. One needs its
  namespace prefix: it is `Precision.JTriple.two_nsmul_of_Y_eq_zero`.

## Summary

- **No Lean declaration in this directory is false or vacuous. None is weaker than a
  consumer needs.**
- **20 articles drifted:** they stated something the Lean does not prove. All 20 are fixed
  in the article prose. Most are details:
  - a missing side condition ($B\ge2$, $m\ge1$, characteristic $\ne2$, natural-valued
    arguments, $k\le\rho_S$);
  - an implementation detail described differently from the Lean definition (division
    block, divmod2, power loop, write-back in the interpreter);
  - routines that do not exist as stated (a rational comparison, point negation,
    multiplication by a constant, zero tests as signed branches).
- **Two articles had a substantively wrong statement:**
  - `programs/lowering-correct.md`: the converse in item 0 is not what `code_backward` proves.
  - `precision/capped-height-test.md`: a remark about intermediate values that is false.
- **Expected extra hypothesis.** `HaltingNodeCheck` is taken by `haltingCircuit_nodeStats`
  (halting-node-check.md, item 1) and `precisionCircuit_nodeStats` (circuit-node-counts.md,
  item 3, and the order remark in item 4). No other declaration in this directory takes a
  hypothesis the article does not state.
- **Lean stronger** in 11 articles (see the table).
- **`lean:` fields are incomplete in about 45 articles:** claims are proved under names that
  are not recorded. No recorded name is wrong or missing from the sources. The largest gap
  is programs/: almost none of the routine contracts (`*_spec`) are recorded, and the
  integer-variable layer (`ZStmt`, `ZStmt.compile_sim`) has no article.

## Verdicts

Lean names are given relative to the namespace of the article's `lean:` field: `ZInQ.AlphaPower`,
`ZInQ.Compiler.Natural`, `ZInQ.Compiler.Packed`, `ZInQ.Compiler.Precision`, `ZInQ.Compiler.IR`,
`ZInQ.Compiler.RM`, `ZInQ.Compiler.Universal`.

### exponential/

| Article | Lean names | Verdict | Changed / to change |
| --- | --- | --- | --- |
| alpha-sequence.md | alphaZ, alphaInt, alphaInt_neg, alphaInt_add_two | faithful; names | Unlisted: `alphaMat`, `alphaMat_mulVec` (the matrix step), `ZInQ.alphaZ_eq_rescaledChebyshev` (Chebyshev remark). |
| alpha-matrix.md | alphaMat_pow, alphaZ_quadratic, alphaZ_addition | faithful; names | Unlisted: `alphaMat_pow_det`, `alphaZ_quadratic_pred`, `alphaZ_isCoprime_succ`, `alphaZ_not_both_even` (item 3). |
| alpha-growth.md | alphaZ_growth, alphaZ_exponential_bounds | faithful; names | Unlisted: `alphaZ_strictMono`, `alphaZ_pos`. |
| alpha-divisibility.md | alphaZ_dvd_alphaZ_iff, alphaZ_sq_dvd_alphaZ_iff | faithful; names | Unlisted: the $k=0$ remark, `alphaZ_sq_dvd_alphaZ_zero_index`. |
| alpha-pell.md | alphaZ_pell_unordered/_ordered/_converse | faithful; names | Unlisted: `alphaZ_pell_index`. |
| alpha-parameter-congruence.md | alphaZ_modEq_of_modEq, alphaZ_modEq_index | faithful; names | Unlisted: `alphaZ_two`. |
| alpha-period.md | alphaZ_period, alphaZ_reflection, alphaZ_folded_residue, two_mul_alphaZ_lt_companion' | Lean stronger; names | Period and reflection do not need $m>0$. Unlisted: `alphaZ_fold_index`, `companion_eq`, `companion_eq_trace`, `two_mul_alphaZ_lt_companion_self`. |
| alpha-large-odd.md | alphaZ_large_odd | faithful | none |
| alpha-equations.md | AlphaEqns | faithful | none |
| alpha-equations-sound.md | alphaEqns_sound | faithful | none |
| alpha-equations-complete.md | alphaEqns_complete, alphaEqns_iff | faithful | none |
| power-equations.md | PowEqns | faithful | none |
| power-equations-correct.md | powEqns_iff | faithful | none |
| binomial-digit.md | ZInQ.binomial_digit_iff_choose | faithful | none |
| lucas-bits.md | lucas_choose_odd_iff_masked, lucas_choose_add_odd_iff_disjoint | faithful | none |
| bit-and.md | bitAnd_gadget_iff, bitAnd_macro_iff | faithful | none |

### formulas/

| Article | Lean names | Verdict | Changed / to change |
| --- | --- | --- | --- |
| natural-atom-gadgets.md | lt/dvd/congr/odd_gadget_iff | faithful; names | Unlisted: the $M=0$ remark, `congr_gadget_zero_iff`. |
| natural-constructions.md | NForm, NM, alpha, power, binomial, orthogonal, mask, bitAnd | faithful; names | Unlisted definitions the article describes: `lt`, `divides`, `congruent`, `odd`, `fresh`, `callPower`, `powerFlat`, `NForm.encode`, `State.init`. |
| natural-circuit-semantics.md | NatCircuit, .poly, .NatRel, .WellScoped | **drift fixed** | The polynomial lies in $\mathbb Z[X_i:i\in\mathbb N]$, not $\mathbb Z[X_0,\dots,X_{V-1}]$. The natural relation sets variables of index $\ge V$ to $0$ (`natPoint`). Both points are now stated. |
| natural-compilation.md | compile_zv_eq_zero_iff, exists_agree_congr, callPower_spec | Lean stronger; names | `exists_agree_congr` holds for any formula whose compilation has variables below $c_1$. `callPower_spec` holds for any well-formed template with 79 witnesses. Unlisted (item 2): `SpecL.cons/and`, `SpecO.cons/or`, `Spec.fresh`, `MSpec.andM/orM/fresh_bind`. |
| macro-semantics.md | lt_spec, divides_spec, alpha_spec, powerSpec_hierarchical, binomial_spec, orthogonal_spec, mask_spec, bitAnd_spec | **drift fixed**; names | Every spec assumes that the argument polynomials take natural values at every natural point (`IsNat`). The article now states this as the hypothesis, and the closing remark explains why it holds. Unlisted: `congruent_spec`, `odd_spec`, `alpha_sem` (the reading $b>3\wedge X=\alpha_b(N)$; `alpha_spec` gives only the equations), `powerSpec_flat'`, `powerSpec_hierarchical_powerTemplate`. |
| hierarchical-calls.md | toCircuit_item1, toCircuit_natRel_iff, toCircuit_natRel_iff_of_mspec, toCircuit_andM_natRel_iff, toCircuit_wellScoped, toCircuit_poly | **drift fixed**; extra hyps (now stated) | Item 2 (`toCircuit_natRel_iff`) has more hypotheses: $k\le V$; the variables of $\kappa(\varphi)$ are below $V$; the call blocks are private (in $[k,\infty)$, pairwise disjoint, avoiding atoms and arguments). It also reads a call through the template's natural relation, which is $g_P=g_Q^{g_R}$ only at natural argument values (`nlift_call_powerTemplate`). Item 2 and its proof sketch now say this. Item 1's `Pres`/`Triple` hypotheses hold for every builder, so they mean "is a construction" and need no change. Item 3 matches. Consumers (register-machine-polynomial, halting-circuit-counts) use items 3 and 1, which are unchanged. |
| power-template.md | powerTemplate, powerTemplate_poly, powerTemplateCircuit_stats | faithful; names | Unlisted: `Universal.powerTemplate_nodeStats` (the constants), `powerTemplateCircuit_varCount`. |
| power-template-semantics.md | powerTemplate_natRel, powerSpec_hierarchical_powerTemplate | **drift fixed** | The "Consequently" sentence (`PowerSpec`) needs natural-valued argument polynomials. That condition is now stated. |

### packed/ and the top-level article

| Article | Lean names | Verdict | Changed / to change |
| --- | --- | --- | --- |
| packed-compiler.md | construction, compiled | faithful | none |
| packed-masks.md | packed_masks | faithful; names | "The digit sequences are unique" is `pack_inj`, which is not listed. |
| packed-state-selection.md | one_active_state | Lean stronger; extra hyp $m\ge1$ (**fixed**) | Lean proves an iff and needs no masking hypothesis. It assumes $0<m$, which the article only implied by naming $S_{m-1}$. The article now says $1\le m<B$. |
| packed-nonzero-indicator.md | nonzero_indicator | faithful | none |
| packed-branches.md | branch_split, indicator_digits | faithful (Lean stronger); names | Lean drops "halt has no outgoing instruction", which is automatic, and allows any $\nu$. Unlisted: `inDigit_le_one` (the $I_i$ digits are $\le1$). |
| packed-transitions.md | packed_register_iff, packed_state_iff | **drift fixed** | `packed_state_iff` needs $B>1$, and the article's standing hypothesis $K<B$ allows $B=1$. Item 2 now begins "Suppose $B\ge2$." Consumers have $B=4K\ge8$. |
| packed-sound.md | packed_sound, packed_sound_accepts | faithful; names | Stated over `PackedConditions`. The link to the formula's relation is `packedRel_conditions`, which is not listed. |
| packed-complete.md | packed_complete | faithful; names | Converse link: `conditions_packedRel`, not listed. |
| packed-counts.md | packed_counts | Lean stronger | No hypotheses at all (no validity, no range for $k$). |
| register-machine-polynomial.md | compiled_natRel_iff | faithful | none |
| natural-polynomial-semantics.md | Compiler.natural_polynomial_semantics, ' | faithful (re-audited) | Unconditional; no `HaltingNodeCheck` premise. |

### precision/

| Article | Lean names | Verdict | Changed / to change |
| --- | --- | --- | --- |
| saturated-arithmetic.md | saturatedArithmetic | faithful | none |
| capped-power.md | cappedArithmetic | faithful | none |
| capped-height-test.md | NExpr.capped_eq, cappedBound_eq, precision_test_iff | **drift fixed**; names | The closing remark said that every intermediate value of the capped evaluation is at most $L+1$. Lean does not prove this, and it is false: a capped sum forms $\langle e_1\rangle+\langle e_2\rangle\le2L+2$ before it saturates. It now says $\beta\le L+1$ and $\langle e\rangle_L\le L+1$ (`cappedBound_le`, `NExpr.capped_le`, both for $L\ge1$, as the article assumes). Unlisted: `divFourLoop_eq`, `cappedBound_le`, `NExpr.capped_le`. |
| decision-program.md | decide5 | faithful; names | Unlisted: `zIdx_eq_nu`, `epsIdx_eq`, `rRatio_eq` (the in-definition identities). |
| decision-program-correct.md | decide5_iff, decideInt_iff | faithful | none |
| jacobian-formulas.md | JTriple.curveE_jdbl, curveE_jadd, jdbl_affine, jadd_affine, jH_eq_zero_iff, jΛ_eq_zero_iff, rep_jdblB, rep_jaddB | **drift fixed**; Lean stronger; names | `jdbl_affine` assumes $2\ne0$; `rep_jdblB`, `rep_jaddB` and `JTriple.two_nsmul_of_Y_eq_zero` assume `NeZero 2`. The article now says "characteristic $\ne2$" in items 3 and 8 and in the sum clause of item 7. Every use is over $K_0$. Lean is stronger elsewhere: items 1–2 hold with explicit cofactors over any commutative ring, and the group law holds for every curve $y^2=x^3+Ax$. Unlisted: `curveE_jdbl_mem`, `curveE_jadd_mem`, `two_nsmul_of_Y_eq_zero`, `rep_jneg`. |
| jacobian-generator.md | curveE_P0J, P0J_affine, rep_P0J | faithful; names | Unlisted: `P0J_Y_sq`, `P0J_rhs`. |
| jacobian-scalar-multiplication.md | rep_jmul, jmul_eq_some, admissible_iff_jmul | faithful; names | Unlisted: `curveE_jmul`, `jmul_Z_eq_zero_iff`, `jmul_Y_eq_zero_iff`. |
| norm-zero.md | rat_eq_zero_of_sq_sub_two_sq, intNorm_ne_zero | faithful; names | Unlisted: `K0.eq_zero_of_norm_eq_zero`, `Zs.norm_ne_zero_iff`, `Zs.mul_star_eq_norm`. |
| precision-guards.md | admissible_of_ne_zero, accepts_iff_tests | Lean stronger | Both are unconditional: "P₀ has infinite order" is discharged by `genP0_not_isOfFinAddOrder`. The forms that take it as a hypothesis are `admissible_of_ne_zero_of` and `accepts_iff_tests_of`. |
| precision-height-constant.md | Q0, A0, sixF, bound, contacts | faithful; names | Unlisted: `ZInQ.heightF0`, `heightD`, `heightG0`, `heightE0`, `heightBcm`, `heightCcm` (formulas match symbolically). |
| precision-height-constant-value.md | A0_eq_heightH6, max_heightD_heightPrimes, bound_eq_heightH6 | faithful; names | Unlisted: `heightD_admissible`, `heightQ_heightD`. |
| precision-relation.md | accepts, acceptsInt, accepts_iff | faithful; names | Unlisted: `precisionTestInt_iff`. |
| precision-threshold.md | four_eps_lt_iff_nat, four_eps_lt_iff, four_eps_mul_pow_lt_one_iff | faithful | none |
| signed-encoding.md | enc, dec, decode5 | faithful | none |
| signed-encoding-bijection.md | dec_enc, enc_dec, encEquiv | faithful; names | Unlisted: `even_enc_iff`, `abs_dec`, `natAbs_dec`. |
| z-coordinate.md | zPt, zPt_ne_zero, Admissible, zIdx, epsIdx, rRatio, rRatio_eq_half_trace | faithful; names | Unlisted: `x_ne_zero_of_y_ne_zero`, `zPt_neg`, `epsIdx_pos`. |

### programs/

| Article | Lean names | Verdict | Changed / to change |
| --- | --- | --- | --- |
| register-machine.md | RM.Instr, Machine, Config, step, Halts, Program, Program.Valid, Program.Accepts | **drift fixed**; names | Register files are arbitrary maps $\mathbb N\to\mathbb N$, not finitely supported. Removed "finitely supported". Unlisted: `Program.HaltsOn`, `Program.toMachine`, `initFile`, `stepN`, `Instr.Valid`, `Program.addCount/subCount`, `Program.Valid.toMachine_eq_halt_iff`. |
| structured-programs.md | IR.Op, Stmt, Outcome, BigStep, BigStep.deterministic, Program, Program.WF, Program.Accepts, Program.Total | **drift fixed** | `Program.WF` also requires $k\le\rho_S$, and the lowering theorems use it. The article now says so. Unlisted: `Stmt.RegsBelow`. |
| cantor-pairing.md | CantorDecoder.pair, decode, encode5, decode5, IR.dec5 | faithful | Unlisted: `CantorDecoder.loop`. |
| cantor-unpairing.md | cantor_pair_props, cantor_unpair_props, cantor_pairing_equation, pairing_system_iff, pairing_system_encode | faithful | none |
| lowering.md | assignB, ltTest, eqTest, code, Stmt.len, code_length, cleanup, lower, lower_length, lower_valid | **drift fixed** | The article said the division block subtracts $z$ while $r\ge z$. The Lean block (`divModB`) instead moves the dividend one unit at a time, with invariant $y=r+qz+m$, $0\le m<z$. Rewrote that sentence. Unlisted: `divModB`, `Program.regCount`. |
| lowering-correct.md | code_forward, code_backward, lower_accepts_of_accepts, accepts_of_lower_halts, lower_halts_iff, lower_accepts_iff, lowering_correct | **drift fixed**; names | **Item 0 was wrong.** The forward direction assumes a machine file that *simulates* $\rho$ (equal below $\rho_S$, zero from $\rho_S$ on). The converse (`code_backward`) is not "a run reaching the normal exit, cleanup or self-loop yields the corresponding derivation". It says: a run from the entry that reaches a halt within $t$ steps yields $\mathbf{accept}$; or a normal outcome plus a halting run within $t$ steps from the normal exit; or $\mathbf{reject}$ plus a halting run from the self-loop. Rewrote item 0 and part (2) of the proof sketch. Items 1–2 are unchanged. Unlisted: `lower_not_halts_of_reject` (it needs no totality). |
| precision-ir.md | precisionZ, precisionProgram, precisionProgram_wf | **drift fixed** | $M=\lvert\kappa F(n)\rvert$ is computed by an integer expression, not by the capped routines; only $\beta$ is. The temporaries come from one shared region, not one region per routine. Both phrases corrected. |
| precision-ir-correct.md | precisionZ_spec, precisionProgram_bigStep, precisionProgram_total, precisionProgram_correct, precisionProgram_accepts_iff | faithful; names | "Reject on a failed early test" is `precisionProgram_reject_of_not_early`, not listed. |
| precision-machine.md | precisionMachine, precRegs, precisionMachine_halts_iff, precisionMachine_accepts_iff, precisionMachine_correct, precisionMachine_valid | **drift fixed**; names | Lean proves that the run never halts (`precisionMachine_not_halts`, not listed), not that it "enters a permanent self-loop". The statement now says "never halts", and the self-loop appears only in the proof sketch. |
| ir-integer-routines.md | SInt, ReprInt, sConst, sCopy, sNeg, sAbs, sAdd, sSub, sMul, sDiv, sMod, sLtFlag, sEqFlag, SContract | **drift fixed**; names | The routines named in the article differ from the Lean ones:<br>• No routine multiplies by a constant, and no routine is a zero test.<br>• The comparisons write a $0/1$ flag rather than branching.<br>• Present but not stated: constant, copy, quotient and remainder of magnitudes, and a natural assignment into a signed result.<br>• The contracts need operand and result registers below a temporary base $t$, and keep only the registers below $t$.<br>The statement is rewritten. I added a paragraph on the integer-variable layer (`ZStmt`, `ZStmt.compile_sim`), which is where the branches live. Unlisted: every `*_spec` (`sDecode_spec`, `sConst_spec`, `sCopy_spec`, `sNeg_spec`, `sAbs_spec`, `sAdd_spec`, `sSub_spec`, `sMul_spec`, `nOp_spec`, `sDiv_spec`, `sMod_spec`, `sLtFlag_spec`, `sEqFlag_spec`), `FlagContract`, `ZStmt`, `ZBigStep`, `ZStmt.compile`, `ReprEnv`, `signedIte_bigStep`, `ZStmt.compile_sim`. |
| ir-field-routines.md | FExpr, FExpr.code, fMul, IExpr, zeroFlag, guardNonzero, intConst, and their specs | **drift fixed**; names | No routine compares two rationals; the closeness test is written with integer expressions. The norm is an integer expression, not a separate routine. The routines are field and integer expressions over integer variables, plus a zero flag and a reject guard. Rewrote the statement with the Lean contracts. Unlisted: `FExpr.assign`, `FExpr.assign_spec`, `natConst`, `natConst_spec`, `IExpr.CodeSpec`, `FExpr.CodeSpec`. |
| ir-point-routines.md | jdblCode, jdblBCode, jaddBCode, jmulCode, and their specs | **drift fixed**; names | No point-negation routine exists; negating $Y$ is inlined in `jmulCode`. The contracts need operand and result triples below $T$, and for the addition a result triple that equals or is disjoint from each operand. The article now says so. Unlisted: `setO_spec`, `setP0_spec`, `copyPt_spec`. |
| ir-capped-routines.md | satCode, cmulCode, cpowCode, cfactCode, caddCode, cmaxCode, cA0Code, cBoundCode, divFourCode, cA0Code_spec, cBoundCode_spec | **drift fixed**; names | `cpowCode` is a loop of $e$ capped multiplications, not binary exponentiation. The final test $x_\beta\ge1$ is not part of `divFourCode`. The contracts are at the integer-variable level, with everything below $T$. Lean is stronger: no $L\ge1$ hypothesis. Unlisted: `satCode_spec`, `cmulCode_spec`, `cpowCode_spec`, `cfactCode_spec`, `divFourCode_spec`, `caddCode_spec`, `cmaxCode_spec`, `satLit_spec`. |
| wrapper-program.md | unpairProgram, wrapperPrefix, relocate, wrapper, wrapper_valid, wrapper_size | Lean stronger | `wrapper_size` also gives $3\le\lvert W\rvert\le200000$ and $r\le2^{18}$. |
| wrapper-correct.md | wrapper_halts_iff_machine, wrapper_halts_iff, wrapper_halts_encode | faithful | none |

### universal/

| Article | Lean names | Verdict | Changed / to change |
| --- | --- | --- | --- |
| program-numbering.md | split2, decodeInstr, decodeMachine, halts, width, code | faithful | Unlisted helper: `digit`. |
| program-numbering-encode.md | decodeMachine_code, halts_code_iff, code_lt, code_ge | Lean stronger | `decodeMachine_code` and `code_lt` need no validity hypothesis. Unlisted: `decodeMachine_code_of_lt/_of_le`. |
| tape-lists.md | cons, uncons, listCode, listCode_bijective, listGet_listSet_self, listSet_listCode, Represents | faithful; names | Unlisted: `cons_bijective`, `uncons_cons`, `cons_uncons`, `tail_lt_cons`, `head_lt_cons`, `listGet_listSet_of_ne`, `listGet_listCode`, `Represents.update`. |
| interpreter-primitives.md | runs_clear, compile_correct_in, runs_copyBlock, runs_addBlock, runs_doubleBlock, runs_divModBlock | **drift fixed**; names | divmod2 *adds* $\lfloor y/2\rfloor$ to $q$ (and sets $r\leftarrow y\bmod2$, $y\leftarrow0$); it does not overwrite $q$. Item 7 now says so, and notes that callers clear $q$ first, as the uncons loop does. Unlisted: the semantic rules `Exec.ifNZ_*`, `Exec.ifLt_*`, `Exec.divmod2`; `reaches_ifLt`, `reaches_divmod2`, `Runs.regs_J`. |
| interpreter-list-primitives.md | runs_unconsBlock, runs_consBlock, runs_getStmt, runs_setStmt | faithful | none |
| universal-interpreter.md | interpreter | **drift fixed** | When $o=2$ and $v=0$, the interpreter still writes $0$ back with setList, which may pad the tape with zeros. Step 3 now says so. Unlisted: `interpreter_eq_compile` (the literal interpreter equals the compiled structured program). |
| interpreter-step.md | interpreter_step, exec_stepStmt | faithful | none |
| interpreter-correct.md | interpreter_accepts_iff | faithful | none |
| interpreter-shape.md | interpreter_shape | faithful | none |
| halting-polynomial.md | haltingCircuit | faithful; names | Unlisted: `haltingCircuit_explicitVars_eq'`, `haltingCircuit_nodes_eq`, `haltingCircuit_consts`. |
| halting-circuit-counts.md | haltingCircuit_counts, haltingCircuit_witnessCount, haltingCircuit_macroCounts | faithful; names | Unlisted: `haltingCircuit_explicitVars_eq'`. |
| halting-node-check.md | HaltingNodeCheck, haltingCircuit_nodeStats, powerTemplate_nodeStats, powerTemplate_nodes_length | extra hyp (expected) | Item 1 is the named check `HaltingNodeCheck`, which `haltingCircuit_nodeStats` takes as a hypothesis. Item 2 is proved by the kernel. The frontmatter has no `proof:` field, so nothing is overclaimed. No change. |
| halting-polynomial-semantics.md | haltingCircuit_natRel_iff, haltingCircuit_natRel_iff_accepts | faithful | none |
| wrapper-size-check.md | wrapper_small, wrapper_valid, wrapper_length | faithful | none |
| wrapper-code-size.md | c3, c3_lt, c3_gt | faithful; names | $c_3<2^{14400019}<2^{2^{24}}$ is `two_pow_14400019_lt` and `c3_lt'`, neither listed. |
| precision-circuit.md | specialize, precisionCircuitOf, precisionCircuit | faithful | Checked node by node against `specialize`. |
| precision-circuit-specialization.md | precisionCircuit_poly, precisionCircuit_natRel_iff, precisionCircuit_wellScoped | Lean stronger | Holds for any call template, not only $\mathcal P$. |
| circuit-node-counts.md | precisionCircuit_counts, precisionCircuitOf_explicitVars, precisionCircuit_nodeStats, precisionCircuit_consts | extra hyp (expected) | Item 3, and the order remark in item 4, come from `precisionCircuit_nodeStats`, which takes `HaltingNodeCheck`. Items 1, 2 and the distinctness in item 4 are unconditional. The article says "from the finite checks on $\mathcal H$", which is accurate. No change. Unlisted: `precisionCircuitOf_nodeStats`, `precisionCircuitOf_constants` (also conditional). |

## Consumer remarks

- No article was weakened below what a consumer uses:
  - The new side conditions ($B\ge2$, $m\ge1$, characteristic $\ne2$, natural-valued
    arguments, $k\le\rho_S$) hold at every use.
  - The routines removed from the programs articles (rational comparison, point negation,
    multiplication by a constant, zero test as a signed branch, binary exponentiation) are
    not used by any consumer. The only articles linking to the routine articles are
    precision-ir.md, precision-ir-correct.md and the README.
- `syntax/recipes/witness-accounting.md` uses items 2–4 of circuit-node-counts.md. Item 3,
  and the order remark in item 4, hold only under `HaltingNodeCheck`, as already recorded in
  `final-audit-2026-11-07.md` (F1).
- natural-circuit-semantics.md no longer says that the polynomial lies in
  $\mathbb Z[X_0,\dots,X_{V-1}]$. Where a consumer needs that, it holds for the specific circuit
  (the hypothesis of `toCircuit_natRel_iff` that the variables lie below $V$; the well-scoped
  constructions).

## Suggestions for the lead

- Add the unlisted names above to the `lean:` fields, starting with the programs/ routine
  contracts.
- The integer-variable layer of the programs (`ZOp`, `ZCond`, `ZStmt`, `ZBigStep`,
  `ZStmt.compile`, `ReprEnv`, `ZStmt.compile_sim`) deserves its own article. For now it is
  described in one paragraph of ir-integer-routines.md.
