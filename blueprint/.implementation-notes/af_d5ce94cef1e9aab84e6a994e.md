# Implementation note: Primitive register programs

- Lean names: `ZInQ.Machine.Instr`, `ZInQ.Machine.Prog`, `ZInQ.Machine.Config`,
  `ZInQ.Machine.step`, `ZInQ.Machine.Prog.Halts`, `ZInQ.Machine.Prog.FinalHaltForm`,
  `ZInQ.Machine.Prog.Accepts`.
- Draft:
  ```lean
  inductive Instr | inc (j k : ℕ) | decb (j k k' : ℕ) | halt
  abbrev Prog := List Instr
  structure Config where (pc : ℕ) (reg : ℕ → ℕ)
  def step (prog : Prog) (c : Config) : Option Config := match prog[c.pc]? with
    | some (.inc j k) => some ⟨k, Function.update c.reg j (c.reg j + 1)⟩
    | some (.decb j k k') => if c.reg j = 0 then some ⟨k', c.reg⟩
        else some ⟨k, Function.update c.reg j (c.reg j - 1)⟩
    | _ => none
  def init (x : List ℕ) : Config := ⟨0, fun i => x.getD i 0⟩
  def Prog.Halts (prog : Prog) (x : List ℕ) : Prop := (StateTransition.eval (step prog) (init x)).Dom
  def Prog.Accepts (prog : Prog) (x : List ℕ) : Prop :=
    ∃ R, ⟨prog.length - 1, R⟩ ∈ StateTransition.eval (step prog) (init x) ∧ ∀ i, R i = 0
  ```
  Registers as functions keep `step` simple; `Function.update` lemmas do the rest.
- Coordination: the natural chapter's packed-history compiler needs exactly this program
  format and acceptance notion (Section 10.1); use one shared definition.
- Mathlib: `StateTransition.eval`, `StateTransition.mem_eval`, `StateTransition.Reaches`
  (checked), `Function.update`.
- Upstream reuse: `lean/ZInQ/PackedRegister.lean` (`packed_register_decode`) is about the
  packed histories, not this definition.
- FINITE COMPUTATION: no.
- Difficulty: low (~60 lines).

Shared design (machine notes): namespace `ZInQ.Machine`, files under
`ZInQKernel/Compiler/Machine/`. Primitive programs as `Array Instr`, configurations
`ℕ × (ℕ →₀ ℕ)` or `ℕ × List ℕ`, one-step function `step : Prog → Config → Option Config`
so that Mathlib's `StateTransition.eval`/`Reaches`/`Respects`/`tr_eval`
(Mathlib/Computability/StateTransition.lean) give runs and simulations. Large programs (the
interpreter, the precision machine, the wrapper) are Lean terms built by functions; their
codes, in particular `c_3`, are never evaluated by any proof.
