import ZInQKernel.Compiler.Programs.ZL
import ZInQKernel.Compiler.Precision.Decision

/-!
# Integer and quadratic-field routines (definitions)

Blueprint: `compiler/natural/programs/ir-field-routines.md` (and the constant and expression
helpers of `ir-integer-routines.md`).

An element `g + h s ∈ ℤ[s]` is held in two consecutive integer variables `(w, w + 1)`. Integer
expressions `IExpr` and `ℤ[s]`-expressions `FExpr` are compiled into integer statements that
evaluate them with temporaries above a base `T`; multiplication uses
`(g + h s)(g' + h' s) = (g g' + 2 h h') + (g h' + h g') s`, conjugation `g + h s ↦ g - h s`.
Large constants are built by Horner's rule in base `64`, so the lowering never increments a
register more than `64` times for a constant.
-/

namespace ZInQ.Compiler.IR

open Precision

/-- `k ← n` by Horner's rule in base `64` (with `f` levels of recursion), temporary `T`. -/
def natConstF : ℕ → ℕ → ℕ → ℕ → ZStmt
  | 0, k, n, _ => .assign k (.const n)
  | f + 1, k, n, T =>
    if n < 64 then .assign k (.const n)
    else natConstF f k (n / 64) T ;;; .assign T (.const 64) ;;; .assign k (.nmul k T) ;;;
      .assign T (.const (n % 64)) ;;; .assign k (.nadd k T)

/-- `k ← n` for a natural constant. -/
def natConst (k n T : ℕ) : ZStmt := natConstF 12 k n T

/-- `k ← c` for an integer constant. -/
def intConst (k : ℕ) (c : ℤ) (T : ℕ) : ZStmt :=
  if c < 0 then natConst k c.natAbs T ;;; .assign k (.neg k) else natConst k c.natAbs T

/-! ### Integer expressions -/

/-- Integer expressions over integer variables. -/
inductive IExpr
  | var (w : ℕ)
  | const (c : ℤ)
  | add (e f : IExpr)
  | sub (e f : IExpr)
  | mul (e f : IExpr)
  | neg (e : IExpr)
  | abs (e : IExpr)
  deriving DecidableEq, Repr

/-- The value of an integer expression. -/
def IExpr.eval (E : ℕ → ℤ) : IExpr → ℤ
  | var w => E w
  | const c => c
  | add e f => e.eval E + f.eval E
  | sub e f => e.eval E - f.eval E
  | mul e f => e.eval E * f.eval E
  | neg e => -e.eval E
  | abs e => |e.eval E|

/-- The location of an operand: a variable is read in place, any other expression is
evaluated into the slot `T`. -/
def IExpr.loc : IExpr → ℕ → ℕ
  | var w, _ => w
  | _, T => T

/-- The code of an operand: nothing for a variable. -/
def IExpr.arg : IExpr → ZStmt → ZStmt
  | var _, _ => .skip
  | _, c => c

/-- `d ← e`, temporaries from `T` (`d` may occur in `e`). -/
def IExpr.code : IExpr → ℕ → ℕ → ZStmt
  | var w, d, _ => .assign d (.copy w)
  | const c, d, T => intConst d c T
  | add e f, d, T => IExpr.arg e (e.code T (T + 2)) ;;; IExpr.arg f (f.code (T + 1) (T + 2)) ;;;
      .assign d (.add (e.loc T) (f.loc (T + 1)))
  | sub e f, d, T => IExpr.arg e (e.code T (T + 2)) ;;; IExpr.arg f (f.code (T + 1) (T + 2)) ;;;
      .assign d (.sub (e.loc T) (f.loc (T + 1)))
  | mul e f, d, T => IExpr.arg e (e.code T (T + 2)) ;;; IExpr.arg f (f.code (T + 1) (T + 2)) ;;;
      .assign d (.mul (e.loc T) (f.loc (T + 1)))
  | neg e, d, T => IExpr.arg e (e.code T (T + 2)) ;;; .assign d (.neg (e.loc T))
  | abs e, d, T => IExpr.arg e (e.code T (T + 2)) ;;; .assign d (.abs (e.loc T))

/-! ### Quadratic-field expressions -/

/-- `ℤ[s]`-expressions; `var w` is the pair `(w, w + 1)`, `int w` the integer variable `w`. -/
inductive FExpr
  | var (w : ℕ)
  | int (w : ℕ)
  | const (a b : ℤ)
  | add (e f : FExpr)
  | sub (e f : FExpr)
  | mul (e f : FExpr)
  | neg (e : FExpr)
  | conj (e : FExpr)
  deriving DecidableEq, Repr

/-- The pair `(w, w + 1)` as an element of `ℤ[s]`. -/
def zsOf (E : ℕ → ℤ) (w : ℕ) : Zs := ⟨E w, E (w + 1)⟩

/-- The value of an `ℤ[s]`-expression. -/
def FExpr.eval (E : ℕ → ℤ) : FExpr → Zs
  | var w => zsOf E w
  | int w => ⟨E w, 0⟩
  | const a b => ⟨a, b⟩
  | add e f => e.eval E + f.eval E
  | sub e f => e.eval E - f.eval E
  | mul e f => e.eval E * f.eval E
  | neg e => -e.eval E
  | conj e => star (e.eval E)

/-- The location of an operand pair. -/
def FExpr.loc : FExpr → ℕ → ℕ
  | var w, _ => w
  | _, T => T

/-- `d ← a · b` on pairs (`d, d + 1` distinct from the operand registers), temporary `T`. -/
def fMul (d a b T : ℕ) : ZStmt :=
  .assign d (.mul a b) ;;; .assign T (.mul (a + 1) (b + 1)) ;;; .assign T (.add T T) ;;;
    .assign d (.add d T) ;;; .assign (d + 1) (.mul a (b + 1)) ;;; .assign T (.mul (a + 1) b) ;;;
    .assign (d + 1) (.add (d + 1) T)

/-- The code of an operand: nothing for a pair variable. -/
def FExpr.arg : FExpr → ZStmt → ZStmt
  | var _, _ => .skip
  | _, c => c

/-- `d ← e` into a fresh pair `d` (distinct from all variables of `e`), temporaries from
`T`. -/
def FExpr.code : FExpr → ℕ → ℕ → ZStmt
  | var w, d, _ => .assign d (.copy w) ;;; .assign (d + 1) (.copy (w + 1))
  | int w, d, _ => .assign d (.copy w) ;;; .assign (d + 1) (.const 0)
  | const a b, d, T => intConst d a T ;;; intConst (d + 1) b T
  | add e f, d, T => FExpr.arg e (e.code T (T + 4)) ;;; FExpr.arg f (f.code (T + 2) (T + 4)) ;;;
      .assign d (.add (e.loc T) (f.loc (T + 2))) ;;;
      .assign (d + 1) (.add (e.loc T + 1) (f.loc (T + 2) + 1))
  | sub e f, d, T => FExpr.arg e (e.code T (T + 4)) ;;; FExpr.arg f (f.code (T + 2) (T + 4)) ;;;
      .assign d (.sub (e.loc T) (f.loc (T + 2))) ;;;
      .assign (d + 1) (.sub (e.loc T + 1) (f.loc (T + 2) + 1))
  | mul e f, d, T => FExpr.arg e (e.code T (T + 4)) ;;; FExpr.arg f (f.code (T + 2) (T + 4)) ;;;
      fMul d (e.loc T) (f.loc (T + 2)) (T + 4)
  | neg e, d, T => FExpr.arg e (e.code T (T + 4)) ;;;
      .assign d (.neg (e.loc T)) ;;; .assign (d + 1) (.neg (e.loc T + 1))
  | conj e, d, T => FExpr.arg e (e.code T (T + 4)) ;;;
      .assign d (.copy (e.loc T)) ;;; .assign (d + 1) (.neg (e.loc T + 1))

/-- `d ← e` for any pair `d` below `T` (computed into `T` first, then copied). -/
def FExpr.assign (d : ℕ) (e : FExpr) (T : ℕ) : ZStmt :=
  e.code T (T + 2) ;;; .assign d (.copy T) ;;; .assign (d + 1) (.copy (T + 1))

/-- The flag `f ← [g + h s = 0]` for the pair at `w`, temporary `T`. -/
def zeroFlag (f w T : ℕ) : ZStmt :=
  .assign f (.const 0) ;;; .assign T (.const 0) ;;;
    .ite (.neq w T) (.ite (.neq (w + 1) T) (.assign f (.const 1)) .skip) .skip

/-- Reject unless the pair at `w` is nonzero (temporaries `T`, `T + 1`). -/
def guardNonzero (w T : ℕ) : ZStmt :=
  zeroFlag T w (T + 1) ;;; .assign (T + 1) (.const 0) ;;; .ite (.neq T (T + 1)) .skip .reject

end ZInQ.Compiler.IR
