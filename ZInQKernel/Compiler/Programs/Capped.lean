import ZInQKernel.Compiler.Programs.Field

/-!
# Capped arithmetic routines (definitions)

Blueprint: `compiler/natural/programs/ir-capped-routines.md`.

All operands are natural numbers (non-negative integer variables) and the cap `L ≥ 1` is held
in a variable `Lv`. The routines compute the saturation `σ_L(x) = min(x, L + 1)`, capped
multiplication `cmul_L` (division-guarded, as `PrecisionAlgorithms.cappedMul`), the capped
power by a loop of capped multiplications (its value is `cpow_L(x, e) = σ_L(x^e)`), the
capped factorial, the capped value `⟨e_A⟩_L` of the precision height constant with shared
subexpressions, the capped bound `β`, and the division-by-four loop.
-/

namespace ZInQ.Compiler.IR

/-- `d ← σ_L(x) = min(x, L + 1)`, temporaries `T`, `T + 1` (the value of `x` is read through its
absolute value, `x · 1`). -/
def satCode (Lv d x T : ℕ) : ZStmt :=
  .assign (T + 1) (.const 1) ;;; .assign T (.nadd Lv (T + 1)) ;;;
    .ite (.nlt T x) (.assign d (.copy T)) (.assign d (.nmul x (T + 1)))

/-- `d ← cmul_L(a, b)`: `0` if `a = 0` or `b = 0`, `L + 1` if `a > ⌊L / b⌋`, else `a b`;
temporaries `T, T + 1, T + 2`. -/
def cmulCode (Lv d a b T : ℕ) : ZStmt :=
  .assign T (.const 0) ;;;
    .ite (.neq a T) (.assign d (.const 0))
      (.ite (.neq b T) (.assign d (.const 0))
        (.assign (T + 1) (.div Lv b) ;;;
          .ite (.nlt (T + 1) a) (.assign (T + 2) (.const 1) ;;; .assign d (.nadd Lv (T + 2)))
            (.assign d (.nmul a b))))

/-- `d ← cpow_L(x, e)` by `e` capped multiplications; slots `T` (result), `T + 1` (counter),
`T + 2` (the constant `1`), temporaries from `T + 3`. -/
def cpowCode (Lv d x e T : ℕ) : ZStmt :=
  .assign T (.const 1) ;;; .assign (T + 1) (.const 0) ;;; .assign (T + 2) (.const 1) ;;;
    .loop (T + 1) e (cmulCode Lv T T x (T + 3) ;;; .assign (T + 1) (.nadd (T + 1) (T + 2))) ;;;
    .assign d (.copy T)

/-- `d ← f_L(n)`, the capped factorial: `n` steps `f ← cmul_L(f, σ_L(i))`; slots `T` (result),
`T + 1` (counter), `T + 2` (the constant `1`), `T + 3` (`σ_L(i)`), temporaries from `T + 4`. -/
def cfactCode (Lv d n T : ℕ) : ZStmt :=
  .assign T (.const 1) ;;; .assign (T + 1) (.const 0) ;;; .assign (T + 2) (.const 1) ;;;
    .loop (T + 1) n
      (.assign (T + 1) (.nadd (T + 1) (T + 2)) ;;; satCode Lv (T + 3) (T + 1) (T + 4) ;;;
        cmulCode Lv T T (T + 3) (T + 4)) ;;;
    .assign d (.copy T)

/-- `d ← σ_L(c)` for a natural literal `c`, temporaries from `T`. -/
def satLit (Lv d c T : ℕ) : ZStmt := natConst T c (T + 1) ;;; satCode Lv d T (T + 1)

/-- `d ← σ_L(a + b)`. -/
def caddCode (Lv d a b T : ℕ) : ZStmt := .assign T (.nadd a b) ;;; satCode Lv d T (T + 1)

/-- `d ← σ_L(max(a, b))`. -/
def cmaxCode (Lv d a b T : ℕ) : ZStmt :=
  .ite (.nlt a b) (.assign T (.copy b)) (.assign T (.copy a)) ;;; satCode Lv d T (T + 1)

/-- `d ← ⟨e_A⟩_L`, the capped value of the precision height constant, with the shared
subexpressions `⟨e_{F₀}⟩_L`, `⟨e_D⟩_L` and `⟨e_D²⟩_L` computed once. Slots `V, …, V + 39`,
temporaries from `V + 40`. -/
def cA0Code (Lv d V : ℕ) : ZStmt :=
  let W := V + 40
  -- F₀ = 324!
  satLit Lv V 324 W ;;; cfactCode Lv (V + 1) V W ;;;
  -- D = F₀ · 3^(256 · F₀⁴)
  satLit Lv (V + 2) 4 W ;;; cpowCode Lv (V + 3) (V + 1) (V + 2) W ;;;
  satLit Lv (V + 4) 256 W ;;; cmulCode Lv (V + 5) (V + 4) (V + 3) W ;;;
  satLit Lv (V + 6) 3 W ;;; cpowCode Lv (V + 7) (V + 6) (V + 5) W ;;;
  cmulCode Lv (V + 8) (V + 1) (V + 7) W ;;;
  -- E₀ = 10 · (D · G₀)²
  satLit Lv (V + 9) 116064000000 W ;;; cmulCode Lv (V + 10) (V + 8) (V + 9) W ;;;
  satLit Lv (V + 11) 2 W ;;; cpowCode Lv (V + 12) (V + 10) (V + 11) W ;;;
  satLit Lv (V + 13) 10 W ;;; cmulCode Lv (V + 14) (V + 13) (V + 12) W ;;;
  -- Q₀ = D^(D · E₀)
  cmulCode Lv (V + 15) (V + 8) (V + 14) W ;;; cpowCode Lv (V + 16) (V + 8) (V + 15) W ;;;
  -- B = D² · 3^(21000 · D²) + 1
  cpowCode Lv (V + 17) (V + 8) (V + 11) W ;;;
  satLit Lv (V + 18) 21000 W ;;; cmulCode Lv (V + 19) (V + 18) (V + 17) W ;;;
  cpowCode Lv (V + 20) (V + 6) (V + 19) W ;;; cmulCode Lv (V + 21) (V + 17) (V + 20) W ;;;
  satLit Lv (V + 22) 1 W ;;; caddCode Lv (V + 23) (V + 21) (V + 22) W ;;;
  -- C = 2B + 4096 (1028 + 5D + 84000 D²)
  cmulCode Lv (V + 24) (V + 11) (V + 23) W ;;;
  satLit Lv (V + 25) 1028 W ;;; satLit Lv (V + 26) 5 W ;;; cmulCode Lv (V + 27) (V + 26) (V + 8) W ;;;
  caddCode Lv (V + 28) (V + 25) (V + 27) W ;;;
  satLit Lv (V + 29) 84000 W ;;; cmulCode Lv (V + 30) (V + 29) (V + 17) W ;;;
  caddCode Lv (V + 31) (V + 28) (V + 30) W ;;;
  satLit Lv (V + 32) 4096 W ;;; cmulCode Lv (V + 33) (V + 32) (V + 31) W ;;;
  caddCode Lv (V + 34) (V + 24) (V + 33) W ;;;
  -- A = (2 · 10¹³) · max(1, max(C, Q₀¹⁷))
  satLit Lv (V + 35) 10000000000000 W ;;; cmulCode Lv (V + 36) (V + 11) (V + 35) W ;;;
  satLit Lv (V + 37) 17 W ;;; cpowCode Lv (V + 38) (V + 16) (V + 37) W ;;;
  cmaxCode Lv (V + 39) (V + 34) (V + 38) W ;;; cmaxCode Lv (V + 39) (V + 22) (V + 39) W ;;;
  cmulCode Lv d (V + 36) (V + 39) W

/-- `d ← β = cmul_L(⟨e_A⟩_L, cpow_L(σ_L(M), 24))`; slots from `V`. -/
def cBoundCode (Lv d M V : ℕ) : ZStmt :=
  cA0Code Lv V (V + 4) ;;; satCode Lv (V + 1) M (V + 4) ;;; natConst (V + 2) 24 (V + 4) ;;;
    cpowCode Lv (V + 3) (V + 1) (V + 2) (V + 4) ;;; cmulCode Lv d V (V + 3) (V + 4)

/-- The division-by-four loop: `x ← ⌊x / 4^β⌋` by `β` divisions; slots `T` (counter), `T + 1`
(`1`), `T + 2` (`4`). -/
def divFourCode (x β T : ℕ) : ZStmt :=
  .assign T (.const 0) ;;; .assign (T + 1) (.const 1) ;;; .assign (T + 2) (.const 4) ;;;
    .loop T β (.assign x (.div x (T + 2)) ;;; .assign T (.nadd T (T + 1)))

end ZInQ.Compiler.IR
