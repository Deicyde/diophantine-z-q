# nat-interpreter: report

All seven leaves are formalized and proved, with no `sorry`, no axioms beyond `propext`,
`Quot.sound`, `Classical.choice`, and no `native_decide`. The work is in
`ZInQKernel/Compiler/Interpreter/` (about 3,000 lines). The root module is
`ZInQKernel/Compiler/Interpreter.lean`, imported from `ZInQKernel.lean`. All names are in
namespace `ZInQ.Compiler.Universal`. The branch also merges `wip/nat-halting` (which includes
`wip/nat-programs`), and `lake build ZInQKernel` succeeds.

## Leaves

| article path | Lean name(s) | status |
| --- | --- | --- |
| `compiler/natural/universal/program-numbering.md` | `split2`, `split2_spec`, `split2_eq_of`, `digit`, `decodeInstr`, `decodeMachine`, `halts`, `instrFields`, `maxField`, `width`, `width_spec`, `fieldsOf`, `codeD`, `codeD_eq_sum`, `code` | proved (definitions + characterizations) |
| `compiler/natural/universal/program-numbering-encode.md` | `decodeMachine_code`, `decodeMachine_code_of_lt`, `decodeMachine_code_of_le`, `halts_code_iff`, `code_lt`, `code_ge` | proved |
| `compiler/natural/universal/tape-lists.md` | `cons`, `uncons`, `uncons_cons`, `cons_uncons`, `cons_inj`, `cons_bijective`, `tail_lt_cons`, `head_lt_cons`, `uncons_snd_lt`, `uncons_fst_lt`, `listCode`, `decodeList`, `listCode_bijective`, `listGet`, `listSet`, `listGet_listSet_self`, `listGet_listSet_of_ne`, `listGet_listCode`, `listSetPad`, `listSet_listCode`, `Represents`, `Represents.update` | proved |
| `compiler/natural/universal/interpreter-primitives.md` | `Stmt.copyBlock`/`runs_copyBlock`, `Stmt.addBlock`/`runs_addBlock`, `Stmt.doubleBlock`/`runs_doubleBlock` (aliased addition), `Stmt.divModBlock`/`runs_divModBlock`, `runs_clear`, the zero test `Exec.ifNZ_pos`/`Exec.ifNZ_zero`, the comparison `Exec.ifLt_lt`/`Exec.ifLt_ge`/`reaches_ifLt`, halving `Exec.divmod2`/`reaches_divmod2`; RM runs from any of these through `Runs.reaches` / `compile_correct_in` | proved |
| `compiler/natural/universal/interpreter-list-primitives.md` | `Stmt.unconsBlock`/`runs_unconsBlock`, `Stmt.consBlock`/`runs_consBlock`, getList = `getStmt`/`runs_getStmt`, setList = `setStmt`/`runs_setStmt` (with `restore`, `saveStep`, `restore_saveStep`) | proved |
| `compiler/natural/universal/interpreter-step.md` | `Coherent`, `CoherentRegs`, `exec_stepStmt` (semantic), `interpreter_step` (machine) | proved |
| `compiler/natural/universal/interpreter-correct.md` | `interpreter_accepts_iff : interpreter.Accepts ![e, n] ↔ halts e n` | proved |

## How the block structure of U was established

The literal `interpreter` (1,399 instructions, from nat-halting) parses completely into a small
structured language. I wrote a throwaway Python decompiler to find this; it is not in the repo.
The language (`Structured.lean`) is `Stmt`:
- `clear`, `inc`, `pred`;
- `seq`;
- `whileDec x body`, compiled as `dec x (L+1) E; body; dec 2 L L`;
- `ifNZ x A B`, the decrement-and-restore test;
- `ifLt a b A B`, the comparison loop `dec b (L+1) E; dec a L (L+2)` that consumes `a` and `b`;
- `divmod2 y q r`, the 8-instruction halving pattern;
- labelled `loop body` with `brk`, `cont` and `exit`, which are jumps `dec 2 t t` to the loop
  end, the loop start, and the cleanup state 1194.

The compiler is `Stmt.compile`, and `Exec` is a big-step semantics with outcomes normal, break,
continue and exit. Increments of register 2 are excluded, so the jump register stays zero
(`Exec.regs_J`). `compile_correct_in` proves once and for all that compiled code placed anywhere
in any machine runs from its first state to the outcome's target. Every configuration before
the target lies in the statement's own code range.

`Program.lean` writes U as a structured program:
- generic blocks parametrized by their registers. Most take a base register `b` and use the
  consecutive scratch registers `b, b+1, …`: copy uses 1 scratch counter, divMod 11, uncons 8,
  cons 11. This is exactly how the original assembler allocated registers;
- six phases: `initStmt`, `fetchStmt`, `opcodeStmt`, `getStmt`, `execStmt` and `setStmt`;
- `bodyStmt = seq stepStmt cont`, `mainStmt = seqs [initStmt, loop bodyStmt]`, and
  `cleanupStmt`, which clears 0..203.

`interpreter_eq_compile : interpreter = interpreterCode` is a kernel comparison of the two
1,399-instruction lists by `decide +kernel`. It takes a few seconds. No run is ever evaluated.
The sizes `initStmt_size = 165`, `stepStmt_size = 1028`, `mainStmt_size = 1194` and
`cleanupStmt_size = 204` are also checked by `decide +kernel`.

Register map: 0 = e, 1 = n, 2 = J, 3 = w, 4 = D, 5 = β, 6 = pc, 7 = tape, 8 = v, 9 = shifted D,
11–14 = o, j, x, y. Loop entry is state 165, the `cont` jump is at 1193, cleanup is 1194–1397,
and the final halt is 1398.

## Statement corrections and deviations

1. **Scratch registers (interpreter-primitives, interpreter-step).** The articles say blocks are
   "entered with … scratch registers zero" and leave "J and the scratch registers zero again",
   and that coherence has "all scratch registers zero". U does not do this. Every block *clears*
   its scratch registers before use, but many are left nonzero afterwards; for example, the
   remainder and quotient registers of `divModBlock` and the quotient register of uncons. The
   Lean statements are stronger on entry and weaker on exit:
   - any initial scratch values are allowed, with only `ρ J = 0` required;
   - the effect on the result registers is stated;
   - every register outside the block's outputs and scratch range is unchanged (`Frame`);
   - scratch values on exit are left unspecified.

   `CoherentRegs` requires J = 0 and leaves scratch arbitrary. It adds that register 3 holds w
   and that every register ≥ 204 is zero. The latter is needed so that cleanup, which clears
   only 0..203, yields an all-zero file. It is maintained through the syntactic `Stmt.writes`
   lemma `Exec.regs_of_not_mem_writes`, together with `stepStmt_writes_lt` and
   `initStmt_writes_lt`, both checked by `decide +kernel`.
2. **divmod** needs only `z ≥ 1`, not `z ≥ 2`. With `z = 0` the block loops forever.
3. **ifLt** in U is the consuming comparison loop on two registers. The "private copies" are
   separate copy blocks inside `divModBlock`. The Lean rule gives the exact final contents:
   `a := 0, b := b - a - 1` when `a < b`, and `a := a - b, b := 0` otherwise.
4. **getList/setList** are proved for the concrete instances used in U (`getStmt`, `setStmt`,
   with U's fixed registers), not as register-generic blocks. uncons, cons and the arithmetic
   blocks are generic.
5. **interpreter-step, item 2.** The Lean statement gives:
   - at least one step;
   - coherence with the virtual successor;
   - "without passing through cleanup", made precise: every configuration up to the return lies
     at a state in `[165, 1194)`.
6. **interpreter-correct, proof.** The (⇒) direction does **not** use items 3–4 of the shape
   check (the predecessors of cleanup). Determinism suffices: each loop iteration takes at least
   one step, so a non-halting virtual run gives coherent configurations at arbitrarily late
   times, and the machine never stops. The proof uses only `interpreter_length` and
   `interpreter_getElem?_last` from `Universal/Shape.lean`. The cleanup structure comes from
   `interpreter_eq_compile`, since `cleanupStmt` sits at 1194 by `mainStmt_size`.
7. **program-numbering-encode.** `decodeMachine_code` holds for every program, valid or not.
   Validity is needed only for `halts_code_iff` and `code_ge`. `code` uses
   `width p = max 2 (Nat.size (maxField p))`, and `width_spec` proves it is the least `w ≥ 2`
   bounding all fields. `codeD` is `Nat.ofDigits (2^w) (fieldsOf p)`, and `codeD_eq_sum` proves
   it equals the article's double sum.
8. **halts** is defined with `initFile ![n]`, the same initial file as `Program.HaltsOn`, rather
   than `Function.update 0 0 n`.

## Lemmas added beyond the leaves

- **Framework (`Structured.lean`):**
  - `Stmt`, `Stmt.size`, `Stmt.compile`, `Stmt.length_compile`, `Stmt.writes`, `Stmt.seqs`,
    `Stmt.Range`;
  - `Outcome`, `Exec`, `Exec.regs_J`, `Exec.regs_of_not_mem_writes`;
  - `Reaches`, `ReachesIn` (with `refl`, `trans`, `mono`, `of_step`, `reaches`);
  - `CodeAt` with its splitting lemmas;
  - `reaches_inc/dec_pos/dec_zero/jump/clear/ifLt/divmod2`;
  - `compile_correct_in`, `compile_correct`.
- **Block library (`Blocks.lean`, `ListBlocks.lean`):** `Runs`, `Frame`, `Scratch`, the tactics
  `regs_ext`, `upd`, `omegaJ`, `frame_scratch`, and `runs_move1`, `runs_move2`, `runs_subLoop`,
  `runs_whileDec`, `runs_divModLoop`, `runs_doubleLoop`, `runs_unconsLoop`.
- **Phases (`Phases.lean`):** `runs_shiftLoop`, `runs_digit`, `runs_fetchStmt`,
  `runs_opcodeStmt`, `exec_opcodeStmt_exit`, `runs_getWalk`, `runs_execStmt` (with `newVal`,
  `newPc`), `runs_saveLoop`, `runs_restoreLoop`.
- **Assembly (`Step.lean`, `Correct.lean`):**
  - `codeAt_*`, `interpreter_toMachine_cont`, `div_pow_mod_eq_digit`;
  - `uncons_succ` (`uncons (e+1) = split2 e`);
  - `exec_initStmt`, `runs_clears`, `runs_cleanupStmt`, `interpreter_init`;
  - `accepts_of_reaches_cleanup`, `stepN_eq_none_of_halt`, `represents_init`.
- **Encoding helpers (`Encode.lean`):** `ofDigits_div_pow_mod`, `getD_mul_pow_le_ofDigits`,
  `fieldsOf_getD`, `fieldsOf_lt`, `valid_step_state_lt`, `valid_stepN_state_lt`, `codeD_lt`.

## Problems

- None blocking.
- Mathlib's cycle notation `c[...]` captures a variable named `c` followed by `[k]`, so avoid
  naming a list `c`.
- `omega` treats the abbreviation `J` (= 2) as an atom; hence the `omegaJ` tactic.

## Suggestions for the next agent

- The blueprint `lean:` fields can point at the names in the table.
- Items 3–4 of `interpreter_shape` are no longer needed for correctness; the proof sketch of
  `interpreter-correct.md` can say "determinism" instead.
- The universal halting circuit's semantics can use `interpreter_accepts_iff` directly, together
  with `halts_code_iff` for the wrapper.
- The same structured-program framework (`Stmt`, `Exec`, `compile_correct_in`) could verify
  other register programs, such as the wrapper or a lowered precision program, if their
  compilers emit the same instruction patterns.
