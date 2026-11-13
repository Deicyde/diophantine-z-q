import ZInQKernel.Compiler.Interpreter.Structured
import ZInQKernel.Compiler.Universal.Interpreter

/-!
# The universal interpreter as a structured program

The literal interpreter `ZInQ.Compiler.Universal.interpreter` (`1,399` instructions over `204`
registers) is the compilation of an explicit structured program assembled from the arithmetic
and list blocks of the interpreter articles: `interpreter_eq_compile` checks the equality of
the two instruction lists in the kernel. This is how the block structure of the literal is
established: each block below is a function of its registers (most blocks take a base register
`b` and use the consecutive scratch registers `b, b + 1, …`), and the structured program fixes
every register exactly as the literal does.

Register map of the interpreter: `0 = e`, `1 = n`, `2 = J` (jump register), `3 = w`, `4 = D`,
`5 = β = 2 ^ w`, `6 = pc`, `7` the tape, `8` the value read, `9` the shifted number,
`11, 12, 13, 14` the digits `o, j, x, y`, and private scratch registers for every block.

(Blueprint: `compiler/natural/universal/universal-interpreter.md`,
`interpreter-primitives.md`, `interpreter-list-primitives.md`.)
-/

namespace ZInQ.Compiler.Universal

open RM

namespace Stmt

/-! ### Arithmetic blocks -/

/-- `x ← y` through the scratch counter `t`. -/
def copyBlock (x y t : ℕ) : Stmt :=
  seqs [clear x, clear t, whileDec y (seqs [inc x, inc t]), whileDec t (inc y)]

/-- `x ← x + y` through the scratch counter `t` (`x ≠ y`). -/
def addBlock (x y t : ℕ) : Stmt :=
  seqs [clear t, whileDec y (seqs [inc x, inc t]), whileDec t (inc y)]

/-- `x ← x + x`: the operand is snapshot into `s` (through `t₁`) before `x` is overwritten. -/
def doubleBlock (x s t₁ t₂ : ℕ) : Stmt := seqs [copyBlock s x t₁, addBlock x s t₂]

/-- `q ← ⌊y / z⌋`, `r ← y mod z` by repeated subtraction from the private remainder `b`,
subtracting only when `b ≥ z`; scratch registers `b, …, b + 10`. -/
def divModBlock (y z q r b : ℕ) : Stmt :=
  seqs [copyBlock b y (b + 3), clear (b + 1),
    loop (seqs [copyBlock (b + 4) b (b + 6), copyBlock (b + 5) z (b + 7),
      ifLt (b + 4) (b + 5) (seqs [brk])
        (seqs [copyBlock (b + 2) z (b + 8), whileDec (b + 2) (pred b), inc (b + 1), cont])]),
    copyBlock q (b + 1) (b + 9), copyBlock r b (b + 10)]

/-! ### List blocks -/

/-- `(h, t) ← uncons x`: copy `x` into `b`, then halve while even, counting in `h`; on an
odd value `2t + 1` the halving quotient is `t`. Scratch registers `b, …, b + 7`. -/
def unconsBlock (x h t b : ℕ) : Stmt :=
  seqs [copyBlock b x (b + 3), clear h,
    ifNZ b
      (loop (seqs [copyBlock (b + 4) b (b + 5), clear (b + 1), divmod2 (b + 4) (b + 1) (b + 2),
        ifNZ (b + 2) (seqs [copyBlock t (b + 1) (b + 6), brk])
          (seqs [inc h, copyBlock b (b + 1) (b + 7), cont])]))
      (clear t)]

/-- `out ← cons h t = 2 ^ h (2t + 1)`, copying both inputs first. Scratch `b, …, b + 10`. -/
def consBlock (h t out b : ℕ) : Stmt :=
  seqs [copyBlock b t (b + 2), doubleBlock b (b + 3) (b + 4) (b + 5), inc b,
    copyBlock (b + 1) h (b + 6), whileDec (b + 1) (doubleBlock b (b + 7) (b + 8) (b + 9)),
    copyBlock out b (b + 10)]

end Stmt

open Stmt

/-! ### The interpreter -/

/-- Decoding `e + 1 = 2 ^ w (2D + 1)` into `w` (register `3`) and `D` (register `4`), exit to
cleanup on `w = 0`, `β = 2 ^ w` (register `5`), `pc = 0` and the tape `cons(n, nil)`. -/
def initStmt : Stmt :=
  seqs [copyBlock 17 0 19, inc 17, unconsBlock 17 3 4 20, ifNZ 3 skip exit,
    clear 5, inc 5, copyBlock 10 3 28, whileDec 10 (doubleBlock 5 29 30 31),
    clear 6, consBlock 1 J 7 32]

/-- Digit extraction: shift `D` by `4 pc` base-`β` digits, then read `o, j, x, y` into
registers `11, 12, 13, 14`. -/
def fetchStmt : Stmt :=
  seqs [copyBlock 9 4 43,
    copyBlock 10 6 44, addBlock 10 6 45, addBlock 10 6 46, addBlock 10 6 47,
    whileDec 10 (seqs [divModBlock 9 5 15 16 48, copyBlock 9 15 59]),
    divModBlock 9 5 15 11 60, copyBlock 9 15 71,
    divModBlock 9 5 15 12 72, copyBlock 9 15 83,
    divModBlock 9 5 15 13 84, copyBlock 9 15 95,
    divModBlock 9 5 15 14 96, copyBlock 9 15 107]

/-- The opcode test: exit to cleanup unless `o ∈ {1, 2}`. -/
def opcodeStmt : Stmt :=
  seqs [copyBlock 18 11 108, ifNZ 18 (pred 18) exit,
    ifNZ 18 (seqs [pred 18, ifNZ 18 exit skip]) skip]

/-- getList: walk `j` links of the tape, then read the head into register `8`. -/
def getStmt : Stmt :=
  seqs [copyBlock 109 7 113, copyBlock 110 12 114,
    whileDec 110 (seqs [unconsBlock 109 111 112 115, copyBlock 109 112 123]),
    unconsBlock 109 8 112 124]

/-- Execute the instruction on the value `v` (register `8`) and set the new `pc`. -/
def execStmt : Stmt :=
  seqs [copyBlock 18 11 132, pred 18,
    ifNZ 18 (ifNZ 8 (seqs [pred 8, copyBlock 6 13 133]) (copyBlock 6 14 134))
      (seqs [inc 8, copyBlock 6 13 135])]

/-- setList: save the traversed prefix in reverse (register `138`), replace the entry by the
value of register `8`, restore the prefix, and store the new tape. -/
def setStmt : Stmt :=
  seqs [copyBlock 136 7 142, copyBlock 137 12 143, clear 138,
    whileDec 137 (seqs [unconsBlock 136 139 140 144, consBlock 139 138 138 152,
      copyBlock 136 140 163]),
    unconsBlock 136 139 140 164, consBlock 8 140 141 172,
    whileDec 138 (seqs [inc 138, unconsBlock 138 139 140 183, consBlock 139 141 141 191,
      copyBlock 138 140 202]),
    copyBlock 7 141 203]

/-- The work of one loop iteration. -/
def stepStmt : Stmt := seqs [fetchStmt, opcodeStmt, getStmt, execStmt, setStmt]

/-- One loop iteration. -/
def bodyStmt : Stmt := seq stepStmt cont

/-- Clear all `204` registers. -/
def cleanupStmt : Stmt := seqs ((List.range 204).map clear)

/-- The interpreter before cleanup: initialization and the main loop. -/
def mainStmt : Stmt := seqs [initStmt, loop bodyStmt]

/-- The first cleanup state. -/
abbrev cleanupEntry : ℕ := 1194

/-- The compiled structured interpreter, followed by the final halt. -/
def interpreterCode : Program :=
  (seq mainStmt cleanupStmt).compile 0 0 0 cleanupEntry ++ [.halt]

/-- **The block structure of the literal interpreter**: it is the compilation of the
structured program (a kernel comparison of two lists of `1,399` instructions). -/
theorem interpreter_eq_compile : interpreter = interpreterCode := by decide +kernel

theorem initStmt_size : initStmt.size = 165 := by decide +kernel

theorem stepStmt_size : stepStmt.size = 1028 := by decide +kernel

theorem mainStmt_size : mainStmt.size = 1194 := by decide +kernel

theorem cleanupStmt_size : cleanupStmt.size = 204 := by decide +kernel

end ZInQ.Compiler.Universal
