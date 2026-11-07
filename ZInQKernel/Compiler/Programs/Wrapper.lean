import ZInQKernel.Compiler.Programs.PrecisionIR
import ZInQKernel.Compiler.Programs.Lowering

/-!
# The precision machine and the wrapper program

Blueprint: `compiler/natural/programs/wrapper-program.md` (and the definition of
`M_prec` in `precision-machine.md`).

`precisionMachine = low(S_prec)` has `r_prec = precisionProgram.regCount` registers. The
prefix `Π` is the open code of the unpairing program `unpairProgram`, whose working
registers (`r_prec`, `r_prec + 1`, `r_prec + 2`), jump register (`r_prec + 3`) and auxiliary
registers (`r_prec + 4, …, r_prec + 9`) are all at indices at least `r_prec`: from the input
`x` in register `0` it runs the Cantor decoder loop four times, places `c₀, …, c₄` in
registers `0, …, 4` and clears its working registers. The wrapper is `Π` followed by
`M_prec` with every target increased by `|Π|`; the normal exit of `Π` is the first state of
the relocated machine, whose final halt is the final halt of the wrapper.
-/

namespace ZInQ.Compiler.IR

open RM

/-- **The precision machine** `M_prec = low(S_prec)`. -/
def precisionMachine : RM.Program := lower precisionProgram

/-- `r_prec`, the register count of the precision machine. -/
def precRegs : ℕ := precisionProgram.regCount

/-- One application of the Cantor decoder: `(s, ρ) ← (0, R)`; while `s < ρ`, `s ← s + 1`,
`ρ ← ρ - s`; then register `i` gets `s - ρ` (the remainder `ρ` stays in `R`). Registers:
`S = B`, `R = B + 1`, `ONE = B + 2`. -/
def unpairStep (B i : ℕ) : Stmt :=
  asg B (.const 0) ;; asg (B + 2) (.const 1) ;;
    .whileLt B (B + 1) (asg B (.add B (B + 2)) ;; asg (B + 1) (.sub (B + 1) B)) ;;
    asg i (.sub B (B + 1))

/-- The unpairing program: `R ← x`, four decoder steps into registers `0, 1, 2, 3`,
register `4 ← R`, and the working registers cleared. -/
def unpairBody (B : ℕ) : Stmt :=
  asg (B + 1) (.copy 0) ;; unpairStep B 0 ;; unpairStep B 1 ;; unpairStep B 2 ;; unpairStep B 3 ;;
    asg 4 (.copy (B + 1)) ;; asg B (.const 0) ;; asg (B + 1) (.const 0) ;; asg (B + 2) (.const 0)

/-- The unpairing program with working registers from `r_prec`. -/
def unpairProgram : Program where
  body := unpairBody precRegs
  bound := precRegs + 3
  inputs := 1

/-- The prefix `Π`: the open code of the unpairing program (jump register `r_prec + 3`). -/
def wrapperPrefix : List Instr := code unpairProgram.bound unpairProgram.body 0 0 0

/-- Increase every target of an instruction by `d`. -/
def relocate (d : ℕ) : Instr → Instr
  | .inc j x => .inc j (x + d)
  | .dec j x y => .dec j (x + d) (y + d)
  | .halt => .halt

/-- **The wrapper** `𝒲 = Π ‖ (M_prec with every target increased by |Π|)`. -/
def wrapper : RM.Program := wrapperPrefix ++ precisionMachine.map (relocate wrapperPrefix.length)

end ZInQ.Compiler.IR
