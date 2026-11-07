import ZInQKernel.Compiler.Programs.Signed

/-!
# The integer layer

The routines of the precision program are written in a small language over integer
variables (`ZStmt`), compiled into the ideal register language by `ZStmt.compile`: integer
variable `k` lives in the signed register pair `(off + 2k, off + 2k + 1)`, every primitive is
one of the signed integer routines of `Signed.lean`, and a test computes a flag into a
temporary register and branches on it. Loops run while `|a| < |b|`. Its big-step semantics `ZBigStep` acts on
environments `ℕ → ℤ`; `ZLSim.lean` proves that the compiled statement simulates it, so the
field, point, capped and precision routines are verified at the level of integers.
-/

namespace ZInQ.Compiler.IR

/-- Right-hand sides over integer variables. `div` and `mod` act on absolute values. -/
inductive ZOp
  | const (c : ℤ)
  | copy (a : ℕ)
  | add (a b : ℕ)
  | sub (a b : ℕ)
  | mul (a b : ℕ)
  | neg (a : ℕ)
  | abs (a : ℕ)
  | div (a b : ℕ)
  | mod (a b : ℕ)
  | nadd (a b : ℕ)
  | nsub (a b : ℕ)
  | nmul (a b : ℕ)
  deriving DecidableEq, Repr

/-- The value of a right-hand side. -/
def ZOp.eval (E : ℕ → ℤ) : ZOp → ℤ
  | const c => c
  | copy a => E a
  | add a b => E a + E b
  | sub a b => E a - E b
  | mul a b => E a * E b
  | neg a => -E a
  | abs a => |E a|
  | div a b => (((E a).natAbs / (E b).natAbs : ℕ) : ℤ)
  | mod a b => (((E a).natAbs % (E b).natAbs : ℕ) : ℤ)
  | nadd a b => (((E a).natAbs + (E b).natAbs : ℕ) : ℤ)
  | nsub a b => (((E a).natAbs - (E b).natAbs : ℕ) : ℤ)
  | nmul a b => (((E a).natAbs * (E b).natAbs : ℕ) : ℤ)

/-- Tests `a < b` and `a = b`, and the same tests on absolute values. -/
inductive ZCond
  | lt (a b : ℕ)
  | eq (a b : ℕ)
  | nlt (a b : ℕ)
  | neq (a b : ℕ)
  deriving DecidableEq, Repr

/-- The truth value of a test. -/
def ZCond.Holds (E : ℕ → ℤ) : ZCond → Prop
  | lt a b => E a < E b
  | eq a b => E a = E b
  | nlt a b => (E a).natAbs < (E b).natAbs
  | neq a b => (E a).natAbs = (E b).natAbs

instance (E : ℕ → ℤ) (c : ZCond) : Decidable (c.Holds E) := by
  cases c <;> unfold ZCond.Holds <;> infer_instance

/-- Statements over integer variables. -/
inductive ZStmt
  | assign (k : ℕ) (o : ZOp)
  | skip
  | seq (s t : ZStmt)
  | ite (c : ZCond) (s t : ZStmt)
  | loop (a b : ℕ) (s : ZStmt)
  | accept
  | reject
  deriving DecidableEq, Repr

/-- Outcomes over integer environments. -/
inductive ZOutcome
  | normal (E : ℕ → ℤ)
  | accept
  | reject

/-- The big-step semantics over integer environments. -/
inductive ZBigStep : ZStmt → (ℕ → ℤ) → ZOutcome → Prop
  | assign (k : ℕ) (o : ZOp) (E : ℕ → ℤ) :
      ZBigStep (.assign k o) E (.normal (Function.update E k (o.eval E)))
  | skip (E : ℕ → ℤ) : ZBigStep .skip E (.normal E)
  | seqNormal {s t : ZStmt} {E E₁ : ℕ → ℤ} {o : ZOutcome} :
      ZBigStep s E (.normal E₁) → ZBigStep t E₁ o → ZBigStep (.seq s t) E o
  | seqAccept {s t : ZStmt} {E : ℕ → ℤ} : ZBigStep s E .accept → ZBigStep (.seq s t) E .accept
  | seqReject {s t : ZStmt} {E : ℕ → ℤ} : ZBigStep s E .reject → ZBigStep (.seq s t) E .reject
  | iteTrue {c : ZCond} {s t : ZStmt} {E : ℕ → ℤ} {o : ZOutcome} :
      c.Holds E → ZBigStep s E o → ZBigStep (.ite c s t) E o
  | iteFalse {c : ZCond} {s t : ZStmt} {E : ℕ → ℤ} {o : ZOutcome} :
      ¬ c.Holds E → ZBigStep t E o → ZBigStep (.ite c s t) E o
  | loopFalse {a b : ℕ} {s : ZStmt} {E : ℕ → ℤ} :
      ¬ (E a).natAbs < (E b).natAbs → ZBigStep (.loop a b s) E (.normal E)
  | loopNormal {a b : ℕ} {s : ZStmt} {E E₁ : ℕ → ℤ} {o : ZOutcome} :
      (E a).natAbs < (E b).natAbs → ZBigStep s E (.normal E₁) → ZBigStep (.loop a b s) E₁ o →
        ZBigStep (.loop a b s) E o
  | loopAccept {a b : ℕ} {s : ZStmt} {E : ℕ → ℤ} :
      (E a).natAbs < (E b).natAbs → ZBigStep s E .accept → ZBigStep (.loop a b s) E .accept
  | loopReject {a b : ℕ} {s : ZStmt} {E : ℕ → ℤ} :
      (E a).natAbs < (E b).natAbs → ZBigStep s E .reject → ZBigStep (.loop a b s) E .reject
  | accept (E : ℕ → ℤ) : ZBigStep .accept E .accept
  | reject (E : ℕ → ℤ) : ZBigStep .reject E .reject

/-- Sequencing of integer statements, written `s ;;; t`. -/
infixr:30 " ;;; " => ZStmt.seq

/-! ### Compilation -/

/-- The register pair of integer variable `k`. -/
def zvar (off k : ℕ) : SInt := ⟨off + 2 * k, off + 2 * k + 1⟩

/-- The signed routine of a right-hand side, writing variable `k`, temporaries from `t`. -/
def ZOp.compile (off k : ℕ) (o : ZOp) (t : ℕ) : Stmt :=
  match o with
  | .const c => sConst (zvar off k) c
  | .copy a => sCopy (zvar off k) (zvar off a) t
  | .add a b => sAdd (zvar off k) (zvar off a) (zvar off b) t
  | .sub a b => sSub (zvar off k) (zvar off a) (zvar off b) t
  | .mul a b => sMul (zvar off k) (zvar off a) (zvar off b) t
  | .neg a => sNeg (zvar off k) (zvar off a) t
  | .abs a => sAbs (zvar off k) (zvar off a) t
  | .div a b => sDiv (zvar off k) (zvar off a) (zvar off b) t
  | .mod a b => sMod (zvar off k) (zvar off a) (zvar off b) t
  | .nadd a b => nOp (zvar off k) (.add (zvar off a).mag (zvar off b).mag) t
  | .nsub a b => nOp (zvar off k) (.sub (zvar off a).mag (zvar off b).mag) t
  | .nmul a b => nOp (zvar off k) (.mul (zvar off a).mag (zvar off b).mag) t

/-- The flag computation of a signed test into register `f`. -/
def flagCode (off : ℕ) (signedEq : Bool) (a b f : ℕ) : Stmt :=
  if signedEq then sEqFlag f (zvar off a) (zvar off b) else sLtFlag f (zvar off a) (zvar off b)

/-- A signed branch: the flag into `t`, zero into `t + 1`, then `if 0 < flag`. -/
def signedIte (off : ℕ) (signedEq : Bool) (a b t : ℕ) (s u : Stmt) : Stmt :=
  flagCode off signedEq a b t ;; asg (t + 1) (.const 0) ;; .ifLt (t + 1) t s u

/-- Compilation into the ideal register language, temporaries from `t`. A test on absolute
values branches directly on the magnitude registers. A signed test computes its flag into
`t`, sets `t + 1` to zero and branches on `0 < flag`; the nested statements then use
temporaries from `t + 2`. -/
def ZStmt.compile (off : ℕ) : ZStmt → ℕ → Stmt
  | .assign k o, t => o.compile off k t
  | .skip, t => asg t (.const 0)
  | .seq s u, t => s.compile off t ;; u.compile off t
  | .ite (.nlt a b) s u, t =>
    .ifLt (zvar off a).mag (zvar off b).mag (s.compile off t) (u.compile off t)
  | .ite (.neq a b) s u, t =>
    .ifEq (zvar off a).mag (zvar off b).mag (s.compile off t) (u.compile off t)
  | .ite (.lt a b) s u, t => signedIte off false a b t (s.compile off (t + 2)) (u.compile off (t + 2))
  | .ite (.eq a b) s u, t => signedIte off true a b t (s.compile off (t + 2)) (u.compile off (t + 2))
  | .loop a b s, t => .whileLt (zvar off a).mag (zvar off b).mag (s.compile off t)
  | .accept, _ => .accept
  | .reject, _ => .reject

/-- The number of temporaries used by the compiled statement. -/
def ZStmt.temps : ZStmt → ℕ
  | .seq s u => max s.temps u.temps
  | .ite (.nlt _ _) s u | .ite (.neq _ _) s u => max s.temps u.temps
  | .ite _ s u => max s.temps u.temps + 2
  | .loop _ _ s => s.temps
  | _ => 6

/-- All variables occurring in the statement are below `K`. -/
def ZOp.VarsBelow (K : ℕ) : ZOp → Prop
  | .const _ => True
  | .copy a | .neg a | .abs a => a < K
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b | .nadd a b | .nsub a b | .nmul a b =>
    a < K ∧ b < K

/-- All variables occurring in a test are below `K`. -/
def ZCond.VarsBelow (K : ℕ) : ZCond → Prop
  | .lt a b | .eq a b | .nlt a b | .neq a b => a < K ∧ b < K

/-- All variables occurring in the statement are below `K`. -/
def ZStmt.VarsBelow (K : ℕ) : ZStmt → Prop
  | .assign k o => k < K ∧ o.VarsBelow K
  | .seq s u => s.VarsBelow K ∧ u.VarsBelow K
  | .ite c s u => c.VarsBelow K ∧ s.VarsBelow K ∧ u.VarsBelow K
  | .loop a b s => a < K ∧ b < K ∧ s.VarsBelow K
  | .skip | .accept | .reject => True

instance (K : ℕ) (o : ZOp) : Decidable (o.VarsBelow K) := by
  cases o <;> unfold ZOp.VarsBelow <;> infer_instance

instance (K : ℕ) (c : ZCond) : Decidable (c.VarsBelow K) := by
  cases c <;> unfold ZCond.VarsBelow <;> infer_instance

end ZInQ.Compiler.IR
