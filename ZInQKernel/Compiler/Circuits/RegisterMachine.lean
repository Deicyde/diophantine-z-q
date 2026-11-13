import Mathlib

/-!
# Register machines

Instructions `inc j x` (increment register `j`, go to state `x`), `dec j x y` (if register `j`
is positive, decrement it and go to `x`; otherwise go to `y`) and `halt`. A machine is a map
from states to instructions; a configuration is a state and a register file `ℕ → ℕ`; the step
function executes the current instruction and is undefined (`none`) at a halt.

A primitive program is a list of instructions. It is valid for `r` registers if it is
nonempty, its last instruction is the only halt, every register index is below `r` and every
target is below its length. It *halts on* inputs `a ∈ ℕ^k` if the run from state `0` and the
initial file reaches the final state, and *accepts* them if it reaches the final state with
every register zero.

(Blueprint: `compiler/natural/programs/register-machine.md`.)
-/

namespace ZInQ.Compiler.RM

/-- Register-machine instructions. -/
inductive Instr
  /-- Increment register `j` and go to state `x`. -/
  | inc (j x : ℕ)
  /-- If register `j` is positive, decrement it and go to `x`; otherwise go to `y`. -/
  | dec (j x y : ℕ)
  /-- Stop. -/
  | halt
  deriving DecidableEq, Repr

/-- A machine assigns an instruction to every state. -/
abbrev Machine : Type := ℕ → Instr

/-- A configuration: the current state and the register file. -/
structure Config where
  /-- The current state. -/
  state : ℕ
  /-- The register file. -/
  regs : ℕ → ℕ

/-- One step of a machine; `none` at a halt instruction. -/
def step (μ : Machine) (c : Config) : Option Config :=
  match μ c.state with
  | .inc j x => some ⟨x, Function.update c.regs j (c.regs j + 1)⟩
  | .dec j x y =>
    if c.regs j = 0 then some ⟨y, c.regs⟩ else some ⟨x, Function.update c.regs j (c.regs j - 1)⟩
  | .halt => none

/-- `n` steps of a machine. -/
def stepN (μ : Machine) : ℕ → Config → Option Config
  | 0, c => some c
  | n + 1, c => (step μ c).bind (stepN μ n)

/-- The run of `μ` from `(0, ρ)` reaches, after finitely many steps, a halt instruction. -/
def Halts (μ : Machine) (ρ : ℕ → ℕ) : Prop :=
  ∃ t c, stepN μ t ⟨0, ρ⟩ = some c ∧ μ c.state = .halt

/-- Primitive programs. -/
abbrev Program : Type := List Instr

/-- A non-final instruction of a program with `m` instructions over `r` registers: not a halt,
register index below `r`, targets below `m`. -/
def Instr.Valid (r m : ℕ) : Instr → Prop
  | .inc j x => j < r ∧ x < m
  | .dec j x y => j < r ∧ x < m ∧ y < m
  | .halt => False

/-- A program is valid for `r` registers: it is nonempty, its last instruction is a halt, and
every other instruction is a non-halt instruction with register index below `r` and targets
below the length. -/
structure Program.Valid (p : Program) (r : ℕ) : Prop where
  pos : 0 < p.length
  last : p[p.length - 1]'(by omega) = .halt
  valid : ∀ i (h : i + 1 < p.length), p[i].Valid r p.length

/-- The machine of a program: `μ(i) = p_i` for `i < m` and `halt` beyond. -/
def Program.toMachine (p : Program) : Machine := fun i => p.getD i .halt

/-- The initial file: `ρ₀(i) = a_i` for `i < k` and `0` otherwise. -/
def initFile {k : ℕ} (a : Fin k → ℕ) : ℕ → ℕ := fun i => if h : i < k then a ⟨i, h⟩ else 0

/-- The run of `p` from `(0, ρ₀)` reaches the final state `m - 1`. -/
def Program.HaltsOn (p : Program) {k : ℕ} (a : Fin k → ℕ) : Prop :=
  ∃ t c, stepN p.toMachine t ⟨0, initFile a⟩ = some c ∧ c.state = p.length - 1

/-- The run of `p` from `(0, ρ₀)` reaches the final state `m - 1` with every register zero. -/
def Program.Accepts (p : Program) {k : ℕ} (a : Fin k → ℕ) : Prop :=
  ∃ t c, stepN p.toMachine t ⟨0, initFile a⟩ = some c ∧ c.state = p.length - 1 ∧
    ∀ j, c.regs j = 0

/-- Increments are add instructions. -/
def Instr.isInc : Instr → Bool
  | .inc _ _ => true
  | _ => false

/-- Decrements are sub instructions. -/
def Instr.isDec : Instr → Bool
  | .dec _ _ _ => true
  | _ => false

/-- The number of add instructions. -/
def Program.addCount (p : Program) : ℕ := p.countP Instr.isInc

/-- The number of sub instructions. -/
def Program.subCount (p : Program) : ℕ := p.countP Instr.isDec

/-! ### Basic facts -/

@[simp] theorem stepN_zero (μ : Machine) (c : Config) : stepN μ 0 c = some c := rfl

theorem stepN_succ (μ : Machine) (n : ℕ) (c : Config) :
    stepN μ (n + 1) c = (step μ c).bind (stepN μ n) := rfl

theorem stepN_add (μ : Machine) (m n : ℕ) (c : Config) :
    stepN μ (m + n) c = (stepN μ m c).bind (stepN μ n) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm, stepN_succ, stepN_succ, Option.bind_assoc]
    congr 1
    funext d
    exact ih d

/-- Taking one more step at the end. -/
theorem stepN_succ' (μ : Machine) (n : ℕ) (c : Config) :
    stepN μ (n + 1) c = (stepN μ n c).bind (step μ) := by
  rw [stepN_add]
  congr 1
  funext d
  rw [stepN_succ]
  cases step μ d <;> rfl

theorem step_eq_none_iff (μ : Machine) (c : Config) : step μ c = none ↔ μ c.state = .halt := by
  unfold step
  split <;> simp_all
  split <;> simp

theorem toMachine_of_lt (p : Program) {i : ℕ} (h : i < p.length) : p.toMachine i = p[i] := by
  simp [Program.toMachine, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem toMachine_of_le (p : Program) {i : ℕ} (h : p.length ≤ i) : p.toMachine i = .halt := by
  simp [Program.toMachine, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- In a valid program the only halting state below the length is the final one. -/
theorem Program.Valid.toMachine_eq_halt_iff {p : Program} {r : ℕ} (hp : p.Valid r) {i : ℕ}
    (hi : i < p.length) : p.toMachine i = .halt ↔ i = p.length - 1 := by
  rw [toMachine_of_lt p hi]
  constructor
  · intro h
    by_contra hne
    have := hp.valid i (by omega)
    rw [h] at this
    exact this
  · rintro rfl
    exact hp.last

theorem initFile_of_lt {k : ℕ} (a : Fin k → ℕ) {i : ℕ} (h : i < k) : initFile a i = a ⟨i, h⟩ := by
  simp [initFile, h]

theorem initFile_of_le {k : ℕ} (a : Fin k → ℕ) {i : ℕ} (h : k ≤ i) : initFile a i = 0 := by
  simp [initFile, show ¬ i < k by omega]

end ZInQ.Compiler.RM
