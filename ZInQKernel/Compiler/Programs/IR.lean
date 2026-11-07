import ZInQKernel.Compiler.Circuits.RegisterMachine

/-!
# The ideal register language

Blueprint: `compiler/natural/programs/structured-programs.md`.

Registers are indexed by `ℕ` and hold natural numbers. Statements are assignments
`x ← k`, `x ← y`, `x ← y + z`, `x ← y ∸ z`, `x ← y · z`, `x ← ⌊y / z⌋`, `x ← y mod z` (Lean's
natural `/` and `%` already satisfy `y / 0 = 0` and `y % 0 = y`), sequencing, the conditionals
`if y < z` and `if y = z`, the loop `while y < z`, and the terminal statements `accept` and
`reject`. The big-step semantics `BigStep S ρ o` relates a statement, a register file and an
outcome; a derivation exists only for terminating executions. The language is deterministic
(`BigStep.deterministic`).
-/

namespace ZInQ.Compiler.IR

/-- The right-hand side of an assignment. -/
inductive Op
  | const (k : ℕ)
  | copy (y : ℕ)
  | add (y z : ℕ)
  | sub (y z : ℕ)
  | mul (y z : ℕ)
  | div (y z : ℕ)
  | mod (y z : ℕ)
  deriving DecidableEq, Repr

/-- The value of a right-hand side in the file `ρ`. -/
def Op.eval (ρ : ℕ → ℕ) : Op → ℕ
  | const k => k
  | copy y => ρ y
  | add y z => ρ y + ρ z
  | sub y z => ρ y - ρ z
  | mul y z => ρ y * ρ z
  | div y z => ρ y / ρ z
  | mod y z => ρ y % ρ z

/-- Statements of the ideal register language. -/
inductive Stmt
  | assign (x : ℕ) (o : Op)
  | seq (s t : Stmt)
  | ifLt (y z : ℕ) (s t : Stmt)
  | ifEq (y z : ℕ) (s t : Stmt)
  | whileLt (y z : ℕ) (s : Stmt)
  | accept
  | reject
  deriving DecidableEq, Repr

/-- Outcomes: normal termination with a file, acceptance, rejection. -/
inductive Outcome
  | normal (ρ : ℕ → ℕ)
  | accept
  | reject

/-- The big-step semantics. -/
inductive BigStep : Stmt → (ℕ → ℕ) → Outcome → Prop
  | assign (x : ℕ) (o : Op) (ρ : ℕ → ℕ) :
      BigStep (.assign x o) ρ (.normal (Function.update ρ x (o.eval ρ)))
  | seqNormal {s t : Stmt} {ρ ρ₁ : ℕ → ℕ} {o : Outcome} :
      BigStep s ρ (.normal ρ₁) → BigStep t ρ₁ o → BigStep (.seq s t) ρ o
  | seqAccept {s t : Stmt} {ρ : ℕ → ℕ} : BigStep s ρ .accept → BigStep (.seq s t) ρ .accept
  | seqReject {s t : Stmt} {ρ : ℕ → ℕ} : BigStep s ρ .reject → BigStep (.seq s t) ρ .reject
  | ifLtTrue {y z : ℕ} {s t : Stmt} {ρ : ℕ → ℕ} {o : Outcome} :
      ρ y < ρ z → BigStep s ρ o → BigStep (.ifLt y z s t) ρ o
  | ifLtFalse {y z : ℕ} {s t : Stmt} {ρ : ℕ → ℕ} {o : Outcome} :
      ¬ ρ y < ρ z → BigStep t ρ o → BigStep (.ifLt y z s t) ρ o
  | ifEqTrue {y z : ℕ} {s t : Stmt} {ρ : ℕ → ℕ} {o : Outcome} :
      ρ y = ρ z → BigStep s ρ o → BigStep (.ifEq y z s t) ρ o
  | ifEqFalse {y z : ℕ} {s t : Stmt} {ρ : ℕ → ℕ} {o : Outcome} :
      ¬ ρ y = ρ z → BigStep t ρ o → BigStep (.ifEq y z s t) ρ o
  | whileFalse {y z : ℕ} {s : Stmt} {ρ : ℕ → ℕ} :
      ¬ ρ y < ρ z → BigStep (.whileLt y z s) ρ (.normal ρ)
  | whileNormal {y z : ℕ} {s : Stmt} {ρ ρ₁ : ℕ → ℕ} {o : Outcome} :
      ρ y < ρ z → BigStep s ρ (.normal ρ₁) → BigStep (.whileLt y z s) ρ₁ o →
        BigStep (.whileLt y z s) ρ o
  | whileAccept {y z : ℕ} {s : Stmt} {ρ : ℕ → ℕ} :
      ρ y < ρ z → BigStep s ρ .accept → BigStep (.whileLt y z s) ρ .accept
  | whileReject {y z : ℕ} {s : Stmt} {ρ : ℕ → ℕ} :
      ρ y < ρ z → BigStep s ρ .reject → BigStep (.whileLt y z s) ρ .reject
  | accept (ρ : ℕ → ℕ) : BigStep .accept ρ .accept
  | reject (ρ : ℕ → ℕ) : BigStep .reject ρ .reject

/-- **Determinism**: each statement and file have at most one outcome. -/
theorem BigStep.deterministic {S : Stmt} {ρ : ℕ → ℕ} {o₁ o₂ : Outcome}
    (h₁ : BigStep S ρ o₁) (h₂ : BigStep S ρ o₂) : o₁ = o₂ := by
  induction h₁ generalizing o₂ with
  | assign => cases h₂; rfl
  | seqNormal _ _ ih₁ ih₂ =>
    cases h₂ with
    | seqNormal h h' => cases ih₁ h; exact ih₂ h'
    | seqAccept h => cases ih₁ h
    | seqReject h => cases ih₁ h
  | seqAccept _ ih =>
    cases h₂ with
    | seqNormal h _ => cases ih h
    | seqAccept => rfl
    | seqReject h => cases ih h
  | seqReject _ ih =>
    cases h₂ with
    | seqNormal h _ => cases ih h
    | seqAccept h => cases ih h
    | seqReject => rfl
  | ifLtTrue hc _ ih =>
    cases h₂ with
    | ifLtTrue _ h => exact ih h
    | ifLtFalse hc' _ => exact absurd hc hc'
  | ifLtFalse hc _ ih =>
    cases h₂ with
    | ifLtTrue hc' _ => exact absurd hc' hc
    | ifLtFalse _ h => exact ih h
  | ifEqTrue hc _ ih =>
    cases h₂ with
    | ifEqTrue _ h => exact ih h
    | ifEqFalse hc' _ => exact absurd hc hc'
  | ifEqFalse hc _ ih =>
    cases h₂ with
    | ifEqTrue hc' _ => exact absurd hc' hc
    | ifEqFalse _ h => exact ih h
  | whileFalse hc =>
    cases h₂ with
    | whileFalse => rfl
    | whileNormal hc' _ _ => exact absurd hc' hc
    | whileAccept hc' _ => exact absurd hc' hc
    | whileReject hc' _ => exact absurd hc' hc
  | whileNormal hc _ _ ih₁ ih₂ =>
    cases h₂ with
    | whileFalse hc' => exact absurd hc hc'
    | whileNormal _ h h' => cases ih₁ h; exact ih₂ h'
    | whileAccept _ h => cases ih₁ h
    | whileReject _ h => cases ih₁ h
  | whileAccept hc _ ih =>
    cases h₂ with
    | whileFalse hc' => exact absurd hc hc'
    | whileNormal _ h _ => cases ih h
    | whileAccept => rfl
    | whileReject _ h => cases ih h
  | whileReject hc _ ih =>
    cases h₂ with
    | whileFalse hc' => exact absurd hc hc'
    | whileNormal _ h _ => cases ih h
    | whileAccept _ h => cases ih h
    | whileReject => rfl
  | accept => cases h₂; rfl
  | reject => cases h₂; rfl

/-- Registers read or written by a right-hand side are below `b`. -/
def Op.RegsBelow (b : ℕ) : Op → Prop
  | .const _ => True
  | .copy y => y < b
  | .add y z | .sub y z | .mul y z | .div y z | .mod y z => y < b ∧ z < b

/-- Every register occurring in the statement is below `b`. -/
def Stmt.RegsBelow (b : ℕ) : Stmt → Prop
  | .assign x o => x < b ∧ o.RegsBelow b
  | .seq s t => s.RegsBelow b ∧ t.RegsBelow b
  | .ifLt y z s t | .ifEq y z s t => y < b ∧ z < b ∧ s.RegsBelow b ∧ t.RegsBelow b
  | .whileLt y z s => y < b ∧ z < b ∧ s.RegsBelow b
  | .accept | .reject => True

theorem Op.RegsBelow.mono {b b' : ℕ} (h : b ≤ b') {o : Op} (ho : o.RegsBelow b) :
    o.RegsBelow b' := by
  cases o <;> simp only [Op.RegsBelow] at ho ⊢ <;> omega

theorem Stmt.RegsBelow.mono {b b' : ℕ} (h : b ≤ b') {S : Stmt} (hS : S.RegsBelow b) :
    S.RegsBelow b' := by
  induction S with
  | assign x o => exact ⟨by have := hS.1; omega, hS.2.mono h⟩
  | seq s t ihs iht => exact ⟨ihs hS.1, iht hS.2⟩
  | ifLt y z s t ihs iht => exact ⟨by have := hS.1; omega, by have := hS.2.1; omega,
      ihs hS.2.2.1, iht hS.2.2.2⟩
  | ifEq y z s t ihs iht => exact ⟨by have := hS.1; omega, by have := hS.2.1; omega,
      ihs hS.2.2.1, iht hS.2.2.2⟩
  | whileLt y z s ih => exact ⟨by have := hS.1; omega, by have := hS.2.1; omega, ih hS.2.2⟩
  | accept => trivial
  | reject => trivial

/-- A program: a statement, a register bound and a number of inputs. -/
structure Program where
  /-- The statement. -/
  body : Stmt
  /-- All registers occurring in the body are below `bound`. -/
  bound : ℕ
  /-- The number of input registers. -/
  inputs : ℕ

/-- A well-formed program: registers below the bound, inputs within the bound. -/
structure Program.WF (P : Program) : Prop where
  regs : P.body.RegsBelow P.bound
  inputs_le : P.inputs ≤ P.bound

/-- The program accepts `a ∈ ℕ^k`: `⟨S, ρ₀(a)⟩ ⇓ accept`. -/
def Program.Accepts (P : Program) (a : Fin P.inputs → ℕ) : Prop :=
  BigStep P.body (RM.initFile a) .accept

/-- The program is total: every input has an outcome. -/
def Program.Total (P : Program) : Prop :=
  ∀ a : Fin P.inputs → ℕ, ∃ o, BigStep P.body (RM.initFile a) o

end ZInQ.Compiler.IR
