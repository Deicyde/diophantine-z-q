import ZInQKernel.Compiler.Programs.IR

/-!
# Signed integer routines (definitions)

Blueprint: `compiler/natural/programs/ir-integer-routines.md`.

An integer `z` is represented by a register pair `(σ, μ)` with `μ = |z|` and `σ = [z < 0]`
(normalized: zero has `σ = 0`). Each routine is a statement of the ideal register language,
parameterized by its operand and result pairs and by a temporary base `t`: it uses the
registers `t, t + 1, …` as temporaries, reads all operands before writing a result, and so
allows results to alias operands. The specifications are in `SignedSpec.lean`.
-/

namespace ZInQ.Compiler.IR

/-- A signed integer register pair. -/
structure SInt where
  /-- The sign register `σ = [z < 0]`. -/
  sign : ℕ
  /-- The magnitude register `μ = |z|`. -/
  mag : ℕ
  deriving DecidableEq, Repr

/-- `(σ, μ)` represents `z` in the file `ρ`. -/
def ReprInt (ρ : ℕ → ℕ) (x : SInt) (z : ℤ) : Prop :=
  ρ x.sign = (if z < 0 then 1 else 0) ∧ ρ x.mag = z.natAbs

/-- Sequencing, written `s ;; t`. -/
infixr:30 " ;; " => Stmt.seq

/-- `x ← o`. -/
abbrev asg (x : ℕ) (o : Op) : Stmt := .assign x o

/-- `g ← g · min(m, 1)` through the temporary `u`: the sign of a zero magnitude is cleared. -/
def normSign (g m u : ℕ) : Stmt :=
  asg u (.const 1) ;; asg u (.sub m u) ;; asg u (.sub m u) ;; asg g (.mul g u)

/-- Decode the natural number in register `c` into the representation of `dec c`:
`σ = c mod 2`, `μ = ⌊(c + σ)/2⌋`. -/
def sDecode (o : SInt) (c t : ℕ) : Stmt :=
  asg t (.const 2) ;; asg (t + 1) (.mod c t) ;; asg (t + 2) (.add c (t + 1)) ;;
    asg (t + 2) (.div (t + 2) t) ;; asg o.sign (.copy (t + 1)) ;; asg o.mag (.copy (t + 2))

/-- `o ← c` for an integer constant `c` (the lowering increments `|c|` times: use only small
constants). -/
def sConst (o : SInt) (c : ℤ) : Stmt :=
  asg o.sign (.const (if c < 0 then 1 else 0)) ;; asg o.mag (.const c.natAbs)

/-- `o ← x`. -/
def sCopy (o x : SInt) (t : ℕ) : Stmt :=
  asg t (.copy x.sign) ;; asg (t + 1) (.copy x.mag) ;; asg o.sign (.copy t) ;;
    asg o.mag (.copy (t + 1))

/-- `o ← -x`. -/
def sNeg (o x : SInt) (t : ℕ) : Stmt :=
  asg t (.const 1) ;; asg t (.sub t x.sign) ;; asg (t + 1) (.copy x.mag) ;;
    normSign t (t + 1) (t + 2) ;; asg o.sign (.copy t) ;; asg o.mag (.copy (t + 1))

/-- `o ← |x|`. -/
def sAbs (o x : SInt) (t : ℕ) : Stmt :=
  asg t (.copy x.mag) ;; asg o.sign (.const 0) ;; asg o.mag (.copy t)

/-- `o ← x + y`: equal signs add magnitudes; opposite signs subtract the smaller magnitude
from the larger and take the sign of the larger; a zero result gets sign `0`. -/
def sAdd (o x y : SInt) (t : ℕ) : Stmt :=
  .ifEq x.sign y.sign
      (asg t (.add x.mag y.mag) ;; asg (t + 1) (.copy x.sign))
      (.ifLt x.mag y.mag
        (asg t (.sub y.mag x.mag) ;; asg (t + 1) (.copy y.sign))
        (asg t (.sub x.mag y.mag) ;; asg (t + 1) (.copy x.sign))) ;;
    normSign (t + 1) t (t + 2) ;; asg o.sign (.copy (t + 1)) ;; asg o.mag (.copy t)

/-- `o ← x - y`, as `x + (-y)` with `-y` in the temporaries `(t, t + 1)`. -/
def sSub (o x y : SInt) (t : ℕ) : Stmt :=
  sNeg ⟨t, t + 1⟩ y (t + 2) ;; sAdd o x ⟨t, t + 1⟩ (t + 2)

/-- `o ← x · y`: multiply magnitudes, sign `σ₁ ⊕ σ₂` unless the product is zero. -/
def sMul (o x y : SInt) (t : ℕ) : Stmt :=
  asg t (.mul x.mag y.mag) ;; asg (t + 1) (.add x.sign y.sign) ;; asg (t + 2) (.const 2) ;;
    asg (t + 1) (.mod (t + 1) (t + 2)) ;; normSign (t + 1) t (t + 2) ;;
    asg o.sign (.copy (t + 1)) ;; asg o.mag (.copy t)

/-- `o ← ⌊|x| / |y|⌋` (a natural number). -/
def sDiv (o x y : SInt) (t : ℕ) : Stmt :=
  asg t (.div x.mag y.mag) ;; asg o.sign (.const 0) ;; asg o.mag (.copy t)

/-- `o ← |x| mod |y|` (a natural number). -/
def sMod (o x y : SInt) (t : ℕ) : Stmt :=
  asg t (.mod x.mag y.mag) ;; asg o.sign (.const 0) ;; asg o.mag (.copy t)

/-- `o ← o'` for a natural right-hand side `o'` (computed into `t`), with sign `0`. -/
def nOp (o : SInt) (o' : Op) (t : ℕ) : Stmt :=
  asg t o' ;; asg o.sign (.const 0) ;; asg o.mag (.copy t)

/-- The flag `f ← [x < y]`: different signs decide; for equal signs `σ`, `x < y` iff
`μx < μy` (for `σ = 0`) or `μy < μx` (for `σ = 1`). -/
def sLtFlag (f : ℕ) (x y : SInt) : Stmt :=
  .ifLt y.sign x.sign (asg f (.const 1))
    (.ifLt x.sign y.sign (asg f (.const 0))
      (.ifLt x.mag y.mag (asg f (.const 1) ;; asg f (.sub f x.sign))
        (.ifLt y.mag x.mag (asg f (.copy x.sign)) (asg f (.const 0)))))

/-- The flag `f ← [x = y]`. -/
def sEqFlag (f : ℕ) (x y : SInt) : Stmt :=
  .ifEq x.sign y.sign (.ifEq x.mag y.mag (asg f (.const 1)) (asg f (.const 0))) (asg f (.const 0))

end ZInQ.Compiler.IR
