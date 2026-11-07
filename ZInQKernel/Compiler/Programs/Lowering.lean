import ZInQKernel.Compiler.Programs.Runs

/-!
# Lowering to primitive programs

Blueprint: `compiler/natural/programs/lowering.md`.

For a program with register bound `J`, registers below `J` keep their meaning, register `J`
is the jump register (always zero, so `dec J x x` jumps to `x`), and the six registers
`J + 1, …, J + 6` are the auxiliary registers `A₀, …, A₅`, shared by all blocks: every block
starts and ends with them zero. A block for an assignment to `x` first snapshots each source
(moves it into two auxiliary registers and moves one back), then clears and writes `x`.

`code J S s acc rej` is the open code of `S` placed at state `s`, with absolute targets; its
length is `S.len` (independent of the placement), its entry is `s` and its normal exit is
`s + S.len`; `accept` jumps to `acc` and `reject` to `rej`. `lower P` closes the code of the
body: state `n = S.len` is a permanent self-loop (the normal exit and the target of `reject`),
states `n + 1, …, n + r` clear the registers `0, …, r - 1` (the cleanup, target of `accept`),
and state `n + r + 1` is the final halt, where `r = J + 7` is the register count.
-/

namespace ZInQ.Compiler.IR

open RM

/-- The auxiliary register `Aᵢ = J + 1 + i`. -/
abbrev aux (J i : ℕ) : ℕ := J + 1 + i

/-- `clear x` at `s`. -/
def clearB (x s : ℕ) : List Instr := [.dec x s (s + 1)]

/-- Move `y` into `d` at `s` (3 instructions). -/
def transfer1 (J y d s : ℕ) : List Instr := [.dec y (s + 1) (s + 3), .inc d (s + 2), jmp J s]

/-- Move `y` into `d` and `e` at `s` (4 instructions). -/
def transfer2 (J y d e s : ℕ) : List Instr :=
  [.dec y (s + 1) (s + 4), .inc d (s + 2), .inc e (s + 3), jmp J s]

/-- Snapshot `y` into `a`, using `b` as scratch (7 instructions): `y` is restored. -/
def snap (J y a b s : ℕ) : List Instr := transfer2 J y a b s ++ transfer1 J b y (s + 4)

/-- `k` increments of `x`, placed from `s + 1`. -/
def incs (x k s : ℕ) : List Instr := (List.range k).map fun i => .inc x (s + i + 2)

/-- Snapshots of `y` into `A₀` and of `z` into `A₂` (14 instructions). -/
def snap2 (J y z s : ℕ) : List Instr := snap J y (aux J 0) (aux J 1) s ++ snap J z (aux J 2) (aux J 1) (s + 7)

/-- Division (`isDiv`) or remainder of `y` by `z` into `x`. With `r = A₀`, `z' = A₂`,
`m = A₃`, `c = A₄`, `q = A₅`, the loop keeps `y = r + q z + m`, `m + c = z`, `c ≥ 1`. -/
def divModB (J x y z : ℕ) (isDiv : Bool) (s : ℕ) : List Instr :=
  let tail := if isDiv then clearB (aux J 0) (s + 47) else transfer1 J (aux J 0) x (s + 47)
  let fin := s + 47 + tail.length
  snap2 J y z s ++ clearB x (s + 14) ++
    [.dec (aux J 2) (s + 16) (s + 47), .inc (aux J 2) (s + 17)] ++
    transfer2 J (aux J 2) (aux J 4) (aux J 1) (s + 17) ++ transfer1 J (aux J 1) (aux J 2) (s + 21) ++
    [.dec (aux J 0) (s + 25) (s + 39), .inc (aux J 3) (s + 26), .dec (aux J 4) (s + 27) (s + 27),
      .dec (aux J 4) (s + 28) (s + 29), .inc (aux J 4) (s + 24), .inc (aux J 5) (s + 30)] ++
    clearB (aux J 3) (s + 30) ++
    transfer2 J (aux J 2) (aux J 4) (aux J 1) (s + 31) ++ transfer1 J (aux J 1) (aux J 2) (s + 35) ++
    [jmp J (s + 24)] ++
    transfer1 J (if isDiv then aux J 5 else aux J 3) x (s + 39) ++
    clearB (aux J 3) (s + 42) ++ clearB (aux J 4) (s + 43) ++ clearB (aux J 5) (s + 44) ++
    clearB (aux J 2) (s + 45) ++ [jmp J fin] ++ tail

/-- The block of an assignment `x ← o` at `s`. -/
def assignB (J x : ℕ) : Op → ℕ → List Instr
  | .const k, s => clearB x s ++ incs x k s
  | .copy y, s => snap J y (aux J 0) (aux J 1) s ++ clearB x (s + 7) ++ transfer1 J (aux J 0) x (s + 8)
  | .add y z, s => snap2 J y z s ++ clearB x (s + 14) ++ transfer1 J (aux J 0) x (s + 15) ++
      transfer1 J (aux J 2) x (s + 18)
  | .sub y z, s => snap2 J y z s ++ clearB x (s + 14) ++ transfer1 J (aux J 0) x (s + 15) ++
      [.dec (aux J 2) (s + 19) (s + 20), .dec x (s + 18) (s + 18)]
  | .mul y z, s => snap2 J y z s ++ clearB x (s + 14) ++ [.dec (aux J 2) (s + 16) (s + 24)] ++
      transfer2 J (aux J 0) x (aux J 1) (s + 16) ++ transfer1 J (aux J 1) (aux J 0) (s + 20) ++
      [jmp J (s + 15)] ++ clearB (aux J 0) (s + 24)
  | .div y z, s => divModB J x y z true s
  | .mod y z, s => divModB J x y z false s

/-- The length of an assignment block. -/
def Op.len : Op → ℕ
  | .const k => k + 1
  | .copy _ => 11
  | .add _ _ => 21
  | .sub _ _ => 20
  | .mul _ _ => 25
  | .div _ _ => 48
  | .mod _ _ => 50

theorem assignB_length (J x : ℕ) (o : Op) (s : ℕ) : (assignB J x o s).length = o.len := by
  cases o <;> simp [assignB, divModB, snap2, snap, transfer1, transfer2, clearB, incs, Op.len]

/-- The test `y < z` at `s`, branching to `th` or `el` (20 instructions). -/
def ltTest (J y z s th el : ℕ) : List Instr :=
  snap2 J y z s ++
    [.dec (aux J 2) (s + 15) (s + 18), .dec (aux J 0) (s + 14) (s + 16),
      .dec (aux J 2) (s + 16) (s + 17), jmp J th,
      .dec (aux J 0) (s + 18) (s + 19), jmp J el]

/-- The test `y = z` at `s`, branching to `th` or `el` (22 instructions). -/
def eqTest (J y z s th el : ℕ) : List Instr :=
  snap2 J y z s ++
    [.dec (aux J 2) (s + 15) (s + 16), .dec (aux J 0) (s + 14) (s + 17),
      .dec (aux J 0) (s + 19) (s + 21),
      .dec (aux J 2) (s + 17) (s + 18), jmp J el,
      .dec (aux J 0) (s + 19) (s + 20), jmp J el,
      jmp J th]

/-- The length of the open code of a statement. -/
def Stmt.len : Stmt → ℕ
  | .assign _ o => o.len
  | .seq s t => s.len + t.len
  | .ifLt _ _ s t => 20 + s.len + 1 + t.len
  | .ifEq _ _ s t => 22 + s.len + 1 + t.len
  | .whileLt _ _ s => 20 + s.len + 1
  | .accept | .reject => 1

/-- The open code of a statement at `s`, with `accept` jumping to `acc` and `reject` to
`rej`. -/
def code (J : ℕ) : Stmt → ℕ → ℕ → ℕ → List Instr
  | .assign x o, s, _, _ => assignB J x o s
  | .seq S T, s, acc, rej => code J S s acc rej ++ code J T (s + S.len) acc rej
  | .ifLt y z S T, s, acc, rej =>
    ltTest J y z s (s + 20) (s + 20 + S.len + 1) ++ code J S (s + 20) acc rej ++
      [jmp J (s + 20 + S.len + 1 + T.len)] ++ code J T (s + 20 + S.len + 1) acc rej
  | .ifEq y z S T, s, acc, rej =>
    eqTest J y z s (s + 22) (s + 22 + S.len + 1) ++ code J S (s + 22) acc rej ++
      [jmp J (s + 22 + S.len + 1 + T.len)] ++ code J T (s + 22 + S.len + 1) acc rej
  | .whileLt y z S, s, acc, rej =>
    ltTest J y z s (s + 20) (s + 20 + S.len + 1) ++ code J S (s + 20) acc rej ++ [jmp J s]
  | .accept, _, acc, _ => [jmp J acc]
  | .reject, _, _, rej => [jmp J rej]

theorem code_length (J : ℕ) (S : Stmt) (s acc rej : ℕ) : (code J S s acc rej).length = S.len := by
  induction S generalizing s with
  | assign x o => exact assignB_length J x o s
  | seq S T ihS ihT => simp [code, Stmt.len, ihS, ihT]
  | ifLt y z S T ihS ihT =>
    simp [code, Stmt.len, ihS, ihT, ltTest, snap2, snap, transfer1, transfer2]; omega
  | ifEq y z S T ihS ihT =>
    simp [code, Stmt.len, ihS, ihT, eqTest, snap2, snap, transfer1, transfer2]; omega
  | whileLt y z S ih =>
    simp [code, Stmt.len, ih, ltTest, snap2, snap, transfer1, transfer2]; omega
  | accept => rfl
  | reject => rfl

/-- The register count of the lowering: registers below `J`, the jump register and six
auxiliary registers. -/
def Program.regCount (P : Program) : ℕ := P.bound + 7

/-- The cleanup stage from state `b`: `dec i (b+i) (b+i+1)` for `i < r`. -/
def cleanup (r b : ℕ) : List Instr := (List.range r).map fun i => .dec i (b + i) (b + i + 1)

/-- **The lowering** `low(S)`: the open code at `0`, the self-loop at `n`, the cleanup from
`n + 1`, the final halt at `n + r + 1`. -/
def lower (P : Program) : RM.Program :=
  code P.bound P.body 0 (P.body.len + 1) P.body.len ++ [jmp P.bound P.body.len] ++
    cleanup P.regCount (P.body.len + 1) ++ [.halt]

theorem lower_length (P : Program) : (lower P).length = P.body.len + P.regCount + 2 := by
  simp [lower, code_length, cleanup]; omega

end ZInQ.Compiler.IR
