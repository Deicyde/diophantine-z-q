import ZInQKernel.Compiler.Programs.Field

/-!
# Point routines (definitions)

Blueprint: `compiler/natural/programs/ir-point-routines.md`.

A Jacobian triple `(X, Y, Z) ∈ ℤ[s]³` is held in six consecutive integer variables
`p, …, p + 5` (`X = (p, p+1)`, `Y = (p+2, p+3)`, `Z = (p+4, p+5)`). The routines compute
the branching doubling `jdblB` and addition `jaddB` of the decision program and the halving
loop `jmul`; every intermediate quantity is computed into its own pair of temporaries, and
the result is copied into the output triple at the end, so outputs may alias inputs.
-/

namespace ZInQ.Compiler.IR

open Precision JTriple

/-- The triple held at `p`. -/
def ptOf (E : ℕ → ℤ) (p : ℕ) : JTriple Zs := ⟨zsOf E p, zsOf E (p + 2), zsOf E (p + 4)⟩

/-- `q ← p` for triples (componentwise copies, in increasing order). -/
def copyPt (q p : ℕ) : ZStmt :=
  .assign q (.copy p) ;;; .assign (q + 1) (.copy (p + 1)) ;;; .assign (q + 2) (.copy (p + 2)) ;;;
    .assign (q + 3) (.copy (p + 3)) ;;; .assign (q + 4) (.copy (p + 4)) ;;;
    .assign (q + 5) (.copy (p + 5))

/-- `q ← O = (1, 1, 0)`. -/
def setO (q : ℕ) : ZStmt :=
  .assign q (.const 1) ;;; .assign (q + 1) (.const 0) ;;; .assign (q + 2) (.const 1) ;;;
    .assign (q + 3) (.const 0) ;;; .assign (q + 4) (.const 0) ;;; .assign (q + 5) (.const 0)

/-- `q ← P₀ᴶ = (3282 - 2320 s, -247440 + 174966 s, 4)`, temporary `T`. -/
def setP0 (q T : ℕ) : ZStmt :=
  intConst q 3282 T ;;; intConst (q + 1) (-2320) T ;;; intConst (q + 2) (-247440) T ;;;
    intConst (q + 3) 174966 T ;;; intConst (q + 4) 4 T ;;; intConst (q + 5) 0 T

/-- The coefficient `A = -11243 + 7950 s` as a constant expression. -/
def fA : FExpr := .const (-11243) 7950

/-- A small natural constant of `ℤ[s]`. -/
def fN (n : ℤ) : FExpr := .const n 0

/-- Jacobian doubling `q ← dbl(p)` (no branching): `M = 3X² + AZ⁴`, `S = 4XY²`,
`X₃ = M² - 2S`, `Y₃ = M(S - X₃) - 8Y⁴`, `Z₃ = 2YZ`; slots `T, …, T + 9`. -/
def jdblCode (p q T : ℕ) : ZStmt :=
  let X := FExpr.var p
  let Y := FExpr.var (p + 2)
  let Z := FExpr.var (p + 4)
  let M := FExpr.var T
  let S := FExpr.var (T + 2)
  let X3 := FExpr.var (T + 4)
  FExpr.assign T (.add (.mul (fN 3) (.mul X X)) (.mul fA (.mul (.mul Z Z) (.mul Z Z)))) (T + 10) ;;;
  FExpr.assign (T + 2) (.mul (.mul (fN 4) X) (.mul Y Y)) (T + 10) ;;;
  FExpr.assign (T + 4) (.sub (.mul M M) (.mul (fN 2) S)) (T + 10) ;;;
  FExpr.assign (T + 6) (.sub (.mul M (.sub S X3)) (.mul (fN 8) (.mul (.mul Y Y) (.mul Y Y))))
    (T + 10) ;;;
  FExpr.assign (T + 8) (.mul (.mul (fN 2) Y) Z) (T + 10) ;;;
  copyPt q (T + 4)

/-- The branching doubling `q ← dbl*(p)`: `O` if `Z = 0` or `Y = 0`. -/
def jdblBCode (p q T : ℕ) : ZStmt :=
  zeroFlag T (p + 4) (T + 1) ;;; zeroFlag (T + 1) (p + 2) (T + 2) ;;;
    .assign T (.nadd T (T + 1)) ;;; .assign (T + 1) (.const 0) ;;;
    .ite (.neq T (T + 1)) (jdblCode p q (T + 2)) (setO q)

/-- The branching addition `r ← p ⊕ q`. With `B = T + 3` the slots are `Z₁²` (`B`), `Z₂²`,
`U₁`, `U₂`, `S₁`, `S₂`, `H`, `Λ` (`B + 14`), the flags `B + 16`, `B + 17`, `B + 18`, and then
`H²`, `H³`, `X₃`, `Y₃`, `Z₃` (`B + 19`, …, `B + 27`). -/
def jaddBCode (p q r T : ℕ) : ZStmt :=
  let B := T + 3
  let W := B + 29
  let X1 := FExpr.var p
  let Y1 := FExpr.var (p + 2)
  let Z1 := FExpr.var (p + 4)
  let X2 := FExpr.var q
  let Y2 := FExpr.var (q + 2)
  let Z2 := FExpr.var (q + 4)
  let Z1s := FExpr.var B
  let Z2s := FExpr.var (B + 2)
  let U1 := FExpr.var (B + 4)
  let U2 := FExpr.var (B + 6)
  let S1 := FExpr.var (B + 8)
  let S2 := FExpr.var (B + 10)
  let H := FExpr.var (B + 12)
  let L := FExpr.var (B + 14)
  let HH := FExpr.var (B + 19)
  let HHH := FExpr.var (B + 21)
  let X3 := FExpr.var (B + 23)
  let generic : ZStmt :=
    FExpr.assign B (.mul Z1 Z1) W ;;; FExpr.assign (B + 2) (.mul Z2 Z2) W ;;;
    FExpr.assign (B + 4) (.mul X1 Z2s) W ;;; FExpr.assign (B + 6) (.mul X2 Z1s) W ;;;
    FExpr.assign (B + 8) (.mul Y1 (.mul Z2s Z2)) W ;;; FExpr.assign (B + 10) (.mul Y2 (.mul Z1s Z1)) W ;;;
    FExpr.assign (B + 12) (.sub U2 U1) W ;;; FExpr.assign (B + 14) (.sub S2 S1) W ;;;
    zeroFlag (B + 16) (B + 12) (B + 17) ;;; .assign (B + 17) (.const 0) ;;;
    .ite (.neq (B + 16) (B + 17))
      (FExpr.assign (B + 19) (.mul H H) W ;;; FExpr.assign (B + 21) (.mul HH H) W ;;;
        FExpr.assign (B + 23) (.sub (.sub (.mul L L) HHH) (.mul (fN 2) (.mul U1 HH))) W ;;;
        FExpr.assign (B + 25) (.sub (.mul L (.sub (.mul U1 HH) X3)) (.mul S1 HHH)) W ;;;
        FExpr.assign (B + 27) (.mul (.mul H Z1) Z2) W ;;;
        copyPt r (B + 23))
      (zeroFlag (B + 18) (B + 14) (B + 19) ;;;
        .ite (.neq (B + 18) (B + 17)) (setO r) (jdblBCode p r (B + 19)))
  zeroFlag T (p + 4) (T + 1) ;;; .assign (T + 1) (.const 0) ;;;
    .ite (.neq T (T + 1))
      (zeroFlag (T + 2) (q + 4) (T + 1) ;;; .assign (T + 1) (.const 0) ;;;
        .ite (.neq (T + 2) (T + 1)) generic (copyPt r p))
      (copyPt r q)

/-- The halving loop: `out ← mul(k)` for the integer variable `k`. Slots: `Π` at `T`, `Θ` at
`T + 6`, the counter `e` at `T + 12`, the bit at `T + 13`, the constants `2, 1, 0` at
`T + 14, T + 15, T + 16`; temporaries from `T + 17`. -/
def jmulCode (k out T : ℕ) : ZStmt :=
  let acc := T
  let base := T + 6
  let e := T + 12
  .assign e (.abs k) ;;; setO acc ;;; setP0 base (T + 17) ;;;
    .assign (T + 14) (.const 2) ;;; .assign (T + 15) (.const 1) ;;; .assign (T + 16) (.const 0) ;;;
    .loop (T + 16) e
      (.assign (T + 13) (.mod e (T + 14)) ;;;
        .ite (.neq (T + 13) (T + 15)) (jaddBCode acc base acc (T + 17)) .skip ;;;
        jdblBCode base base (T + 17) ;;;
        .assign e (.div e (T + 14))) ;;;
    .ite (.lt k (T + 16)) (.assign (acc + 2) (.neg (acc + 2)) ;;; .assign (acc + 3) (.neg (acc + 3)))
      .skip ;;;
    copyPt out acc

end ZInQ.Compiler.IR
