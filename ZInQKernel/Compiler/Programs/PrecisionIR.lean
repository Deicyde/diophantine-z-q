import ZInQKernel.Compiler.Programs.Point
import ZInQKernel.Compiler.Programs.Capped

/-!
# The precision program

Blueprint: `compiler/natural/programs/precision-ir.md`.

The precision program follows the exact decision program `Precision.decide5` step by step.
The integer program `precisionZ` works on integer variables:

* `0, …, 4`: the decoded inputs `n, κ, a, l, j`;
* `5, 6, 7, 8`: the constants `0, 1, 3, 4`;
* `10`, `16`, `22`: the triples `mul(l)`, `mul(a)`, `mul(j)`; `28`: the work triple;
* `34`: the loop counter, `35`: the current index `k`;
* `36`: `F(n)`; `37`, `38`: `n a` and the test of `j`;
* `40`, `42`, `44`: `ν_l`, `ν_a`, `ν_j`; `46, 47, 48`: `N_l, N_a, N_j`; `49`: `N(ν_a)`;
* `50`: `U`, `51`: `V`, `52`: `δ`, `54`: `θ` (the pair `54, 55`), `56`: `|θ - nδ|V`,
  `57`: `U|δ|`, `58`: `V ∸ 1`, `59`: `4U`, `60`: `L`, `61`: `M`, `62`: `β`, `63`: `x`;
* temporaries from `64`.

The three scalar multiplications run in one loop over the counter (one copy of the halving
code). The register program `precisionProgram` decodes the five input registers into the
signed pairs of variables `0, …, 4` (`sDecode`) and runs the compiled integer program, with
integer variable `k` in registers `5 + 2k, 5 + 2k + 1`.
-/

namespace ZInQ.Compiler.IR

/-- The first temporary variable of the precision program. -/
def precT : ℕ := 64

/-- The three scalar multiplications: `mul(l)`, `mul(a)`, `mul(j)` into `10`, `16`, `22`. -/
def jmul3Code : ZStmt :=
  .assign 34 (.const 0) ;;;
    .loop 34 7
      (.ite (.neq 34 5) (.assign 35 (.copy 3)) (.ite (.neq 34 6) (.assign 35 (.copy 2))
          (.assign 35 (.copy 4))) ;;;
        jmulCode 35 28 precT ;;;
        .ite (.neq 34 5) (copyPt 10 28) (.ite (.neq 34 6) (copyPt 16 28) (copyPt 22 28)) ;;;
        .assign 34 (.nadd 34 6))

/-- The early tests: reject unless `F(n) ≠ 0` (that is `n ∉ 𝒞`), `κ ≠ 0`, `a ≥ 1`, `l ≥ 1`
and `j = n a`. -/
def earlyCode : ZStmt :=
  IExpr.code (.mul (.mul (.mul (.mul (.mul (.var 0) (.add (.var 0) (.const 15)))
      (.add (.var 0) (.const 20))) (.add (.var 0) (.const 24))) (.add (.var 0) (.const 30)))
      (.add (.var 0) (.const 60))) 36 precT ;;;
    .ite (.neq 36 5) .reject .skip ;;;
    .ite (.neq 1 5) .reject .skip ;;;
    .ite (.lt 2 6) .reject .skip ;;;
    .ite (.lt 3 6) .reject .skip ;;;
    .assign 37 (.mul 0 2) ;;; .ite (.eq 4 37) .skip .reject

/-- `N = N(Y) = Y_re² - 2 Y_im²` of the pair at `w`, as an integer expression. -/
def normI (w : ℕ) : IExpr :=
  .sub (.mul (.var w) (.var w)) (.mul (.const 2) (.mul (.var (w + 1)) (.var (w + 1))))

/-- The closeness test and the precision test, after the scalar multiplications. -/
def testCode : ZStmt :=
  -- reject on a zero third or second coordinate
  guardNonzero 14 precT ;;; guardNonzero 20 precT ;;; guardNonzero 26 precT ;;;
  guardNonzero 12 precT ;;; guardNonzero 18 precT ;;; guardNonzero 24 precT ;;;
  -- ν_k = -(X Z Ȳ), N_k = N(Y_k)
  FExpr.assign 40 (.neg (.mul (.mul (.var 10) (.var 14)) (.conj (.var 12)))) precT ;;;
  FExpr.assign 42 (.neg (.mul (.mul (.var 16) (.var 20)) (.conj (.var 18)))) precT ;;;
  FExpr.assign 44 (.neg (.mul (.mul (.var 22) (.var 26)) (.conj (.var 24)))) precT ;;;
  IExpr.code (normI 12) 46 precT ;;; IExpr.code (normI 18) 47 precT ;;;
  IExpr.code (normI 24) 48 precT ;;; IExpr.code (normI 42) 49 precT ;;;
  -- U, V, δ, θ
  IExpr.code (.add (.abs (.var 40)) (.abs (.var 41))) 50 precT ;;;
  IExpr.code (.abs (.var 46)) 51 precT ;;;
  IExpr.code (.mul (.var 48) (.var 49)) 52 precT ;;;
  FExpr.assign 54 (.mul (.mul (.var 44) (.conj (.var 42))) (.int 47)) precT ;;;
  -- the closeness test |θ - nδ| V < U |δ|
  IExpr.code (.mul (.abs (.sub (.var 54) (.mul (.var 0) (.var 52)))) (.var 51)) 56 precT ;;;
  IExpr.code (.mul (.var 50) (.abs (.var 52))) 57 precT ;;;
  .ite (.lt 56 57) .skip .reject ;;;
  -- L = ⌊(V - 1) / (4U)⌋, reject if L = 0
  .assign 58 (.nsub 51 6) ;;; .assign 59 (.nmul 8 50) ;;; .assign 60 (.div 58 59) ;;;
  .ite (.neq 60 5) .reject .skip ;;;
  -- M = |κ F(n)|, β, the division-by-four loop, the final test
  IExpr.code (.abs (.mul (.var 1) (.var 36))) 61 precT ;;;
  cBoundCode 60 62 61 precT ;;;
  .assign 63 (.copy 60) ;;; divFourCode 63 62 precT ;;;
  .ite (.nlt 5 63) .accept .reject

/-- **The precision program** over integer variables. -/
def precisionZ : ZStmt :=
  .assign 5 (.const 0) ;;; .assign 6 (.const 1) ;;; .assign 7 (.const 3) ;;; .assign 8 (.const 4) ;;;
    earlyCode ;;; jmul3Code ;;; testCode

/-- The number of integer variables of `precisionZ` (an upper bound for the variables it
uses). -/
def precisionVars : ℕ := 400

/-- The register offset of the integer variables: registers `0, …, 4` hold the inputs. -/
def precOff : ℕ := 5

/-- Decode the five inputs into the signed pairs of variables `0, …, 4`. -/
def decodeInputs (t : ℕ) : Stmt :=
  sDecode (zvar precOff 0) 0 t ;; sDecode (zvar precOff 1) 1 t ;; sDecode (zvar precOff 2) 2 t ;;
    sDecode (zvar precOff 3) 3 t ;; sDecode (zvar precOff 4) 4 t

/-- The first temporary register of the compiled program. -/
def precRegT : ℕ := precOff + 2 * precisionVars

/-- **The precision program** `S_prec`: five inputs, the decoding, then the compiled integer
program. -/
def precisionProgram : Program where
  body := decodeInputs precRegT ;; precisionZ.compile precOff precRegT
  bound := precRegT + precisionZ.temps + 8
  inputs := 5

end ZInQ.Compiler.IR
