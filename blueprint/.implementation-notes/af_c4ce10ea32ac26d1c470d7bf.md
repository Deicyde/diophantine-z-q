# Implementation note: The universal interpreter

- Lean names: `ZInQ.Machine.interpStmt : Stmt`, `ZInQ.Machine.universalInterpreter : Prog :=
  lower interpStmt`, `ZInQ.Machine.UAccepts (e n : ℕ) : Prop := universalInterpreter.Accepts [e, n]`.
- Draft: write `interpStmt` with macro-level helpers (`halveWhileEven`, `digitAt`, `tapeGet`,
  `tapeSet` as `Stmt` subprograms using fixed scratch registers).
- Size check (cross-check, not a proof obligation unless the syntax counts depend on it):
  `universalInterpreter.length = 1399` and the register bound `204`, by `decide` on the
  concrete program; these numbers must match upstream for the natural chapter's compiled
  polynomial to have the saved shape (see the lowering note).
- Mathlib: none.
- Upstream reuse: none in `lean/ZInQ`; mirror the archived interpreter generator
  (`universal-interpreter-spec.txt` and its generator, research archive) to reproduce the saved
  program.
- FINITE COMPUTATION: the size check only (small: 1,399 instructions, `decide`).
- Difficulty: medium (~200 lines of definitions).

Shared design (machine notes): namespace `ZInQ.Machine`, files under
`ZInQKernel/Compiler/Machine/`. Primitive programs as `Array Instr`, configurations
`ℕ × (ℕ →₀ ℕ)` or `ℕ × List ℕ`, one-step function `step : Prog → Config → Option Config`
so that Mathlib's `StateTransition.eval`/`Reaches`/`Respects`/`tr_eval`
(Mathlib/Computability/StateTransition.lean) give runs and simulations. Large programs (the
interpreter, the precision machine, the wrapper) are Lean terms built by functions; their
codes, in particular `c_3`, are never evaluated by any proof.
