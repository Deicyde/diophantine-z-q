import ZInQKernel.Compiler.Precision.HeightConstant
import ZInQKernel.Compiler.Precision.Saturation

/-!
# The capped precision test

Blueprint: `compiler/natural/precision/capped-height-test.md`.

Natural-number expressions `NExpr` (literals, `+`, `·`, `max`, powers, factorials) have a value
`eval` and, at a cap `L`, a capped value `capped L` computed with saturated operations. The
precision expression `eA` is the displayed expression of `A⁽⁰⁾_ht`; its value is `A0`
(proved by rewriting, never by evaluation). With `β = cmul_L(⟨e_A⟩_L, cpow_L(σ_L(M), 24))` the
division-by-four loop from `L` for `β` steps ends at `⌊L / 4^β⌋`, which is positive exactly when
`4^(A⁽⁰⁾_ht M²⁴) ≤ L`.
-/

namespace ZInQ.Compiler.Precision

open PrecisionArithmetic PrecisionAlgorithms

/-- Natural-number expressions with literals, `+`, `·`, `max`, powers and factorials. -/
inductive NExpr
  | lit (c : ℕ)
  | add (a b : NExpr)
  | mul (a b : NExpr)
  | max (a b : NExpr)
  | pow (a b : NExpr)
  | fact (a : NExpr)
  deriving DecidableEq, Repr

namespace NExpr

/-- The value `⟦e⟧` of an expression. -/
def eval : NExpr → ℕ
  | lit c => c
  | add a b => a.eval + b.eval
  | mul a b => a.eval * b.eval
  | max a b => Max.max a.eval b.eval
  | pow a b => a.eval ^ b.eval
  | fact a => a.eval.factorial

@[simp] theorem eval_lit (c : ℕ) : (lit c).eval = c := rfl
@[simp] theorem eval_add (a b : NExpr) : (add a b).eval = a.eval + b.eval := rfl
@[simp] theorem eval_mul (a b : NExpr) : (mul a b).eval = a.eval * b.eval := rfl
@[simp] theorem eval_max (a b : NExpr) : (max a b).eval = Max.max a.eval b.eval := rfl
@[simp] theorem eval_pow (a b : NExpr) : (pow a b).eval = a.eval ^ b.eval := rfl
@[simp] theorem eval_fact (a : NExpr) : (fact a).eval = a.eval.factorial := rfl

end NExpr

/-- The capped factorial `f_L(0) = 1`, `f_L(n+1) = cmul_L(f_L(n), σ_L(n+1))`. -/
def cappedFact (L : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => cappedMul L (cappedFact L n) (saturate L (n + 1))

namespace NExpr

/-- The capped value `⟨e⟩_L`. -/
def capped (L : ℕ) : NExpr → ℕ
  | lit c => saturate L c
  | add a b => saturate L (a.capped L + b.capped L)
  | mul a b => cappedMul L (a.capped L) (b.capped L)
  | max a b => saturate L (Max.max (a.capped L) (b.capped L))
  | pow a b => cappedPower L (a.capped L) (b.capped L)
  | fact a => cappedFact L (a.capped L)

end NExpr

theorem cappedFact_eq (L n : ℕ) : cappedFact L n = saturate L n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cappedFact, ih, cappedMul_eq_saturate, saturate_mul, Nat.factorial_succ, Nat.mul_comm]

/-- `σ_L((σ_L n)!) = σ_L(n!)`. -/
theorem saturate_factorial_saturate (L n : ℕ) :
    saturate L (saturate L n).factorial = saturate L n.factorial := by
  by_cases hn : n ≤ L + 1
  · rw [saturate_eq_self L n hn]
  · rw [saturate_eq_cap L n (by omega), saturate_eq_cap L _ (Nat.self_le_factorial _),
      saturate_eq_cap L _ (le_trans (by omega) (Nat.self_le_factorial n))]

/-- Item 1: `⟨e⟩_L = σ_L(⟦e⟧)` for `L ≥ 1`. -/
theorem NExpr.capped_eq (L : ℕ) (hL : 1 ≤ L) (e : NExpr) : e.capped L = saturate L e.eval := by
  induction e with
  | lit c => rfl
  | add a b iha ihb => rw [capped, eval, iha, ihb, saturate_add]
  | mul a b iha ihb => rw [capped, eval, iha, ihb, cappedMul_eq_saturate, saturate_mul]
  | max a b iha ihb => rw [capped, eval, iha, ihb, saturate_max]
  | pow a b iha ihb =>
    rw [capped, eval, iha, ihb, cappedPower_eq_saturate, saturate_pow_saturate L _ _ hL]
  | fact a iha => rw [capped, eval, iha, cappedFact_eq, saturate_factorial_saturate]

/-- Every capped value is at most `L + 1`. -/
theorem NExpr.capped_le (L : ℕ) (hL : 1 ≤ L) (e : NExpr) : e.capped L ≤ L + 1 := by
  rw [NExpr.capped_eq L hL]; exact saturate_le_cap L _

/-! ### The precision expression -/

namespace NExpr

open NExpr (lit)

/-- `e_{F₀} = 324!`. -/
def eF0 : NExpr := fact (lit 324)
/-- `e_D = e_{F₀} · 3^(256 · e_{F₀}⁴)`. -/
def eD : NExpr := mul eF0 (pow (lit 3) (mul (lit 256) (pow eF0 (lit 4))))
/-- `e_{G₀} = 116064000000`. -/
def eG0 : NExpr := lit 116064000000
/-- `e_{E₀} = 10 · (e_D · e_{G₀})²`. -/
def eE0 : NExpr := mul (lit 10) (pow (mul eD eG0) (lit 2))
/-- `e_{Q₀} = e_D^(e_D · e_{E₀})`. -/
def eQ0 : NExpr := pow eD (mul eD eE0)
/-- `e_B = e_D² · 3^(21000 · e_D²) + 1`. -/
def eB : NExpr := add (mul (pow eD (lit 2)) (pow (lit 3) (mul (lit 21000) (pow eD (lit 2))))) (lit 1)
/-- `e_C = 2 · e_B + 4096 · (1028 + 5 · e_D + 84000 · e_D²)`. -/
def eC : NExpr :=
  add (mul (lit 2) eB)
    (mul (lit 4096) (add (add (lit 1028) (mul (lit 5) eD)) (mul (lit 84000) (pow eD (lit 2)))))
/-- `e_A = 2 · 10¹³ · max(1, max(e_C, e_{Q₀}¹⁷))`, with the literal `10¹³ = 10000000000000`. -/
def eA : NExpr :=
  mul (mul (lit 2) (lit 10000000000000)) (max (lit 1) (max eC (pow eQ0 (lit 17))))

theorem eval_eF0 : eF0.eval = heightF0 := by rw [eF0, eval_fact, eval_lit, heightF0_eq]

theorem eval_eD : eD.eval = heightD := by
  rw [eD, eval_mul, eval_pow, eval_mul, eval_pow, eval_lit, eval_lit, eval_lit, eval_eF0,
    heightD_eq]

theorem eval_eE0 : eE0.eval = heightE0 := by
  rw [eE0, eval_mul, eval_pow, eval_mul, eval_lit, eval_lit, eval_eD, eG0, eval_lit,
    heightE0_eq, heightG0]

theorem eval_eQ0 : eQ0.eval = Q0 := by
  rw [eQ0, eval_pow, eval_mul, eval_eD, eval_eE0, Q0_eq]

theorem eval_eB : eB.eval = heightBcm := by
  rw [eB, eval_add, eval_mul, eval_pow, eval_pow, eval_mul, eval_pow, eval_lit, eval_lit,
    eval_lit, eval_lit, eval_eD, heightBcm_eq]

theorem eval_eC : eC.eval = heightCcm := by
  rw [eC, eval_add, eval_mul, eval_mul, eval_add, eval_add, eval_mul, eval_mul, eval_pow,
    eval_lit 2, eval_lit 4096, eval_lit 1028, eval_lit 5, eval_lit 84000, eval_eB,
    eval_eD, heightCcm_eq]

theorem ten_pow_thirteen : (10 : ℕ) ^ 13 = 10000000000000 := by norm_num

/-- `⟦e_A⟧ = A⁽⁰⁾_ht`. -/
theorem eval_eA : eA.eval = A0 := by
  rw [eA, eval_mul, eval_mul, eval_max, eval_max, eval_pow, eval_lit, eval_lit, eval_lit,
    eval_lit, eval_eC, eval_eQ0, A0_eq, ten_pow_thirteen]

end NExpr

/-! ### The capped bound and the division-by-four loop -/

/-- `β = cmul_L(⟨e_A⟩_L, cpow_L(σ_L(M), 24))`. -/
def cappedBound (L M : ℕ) : ℕ :=
  cappedMul L (NExpr.eA.capped L) (cappedPower L (saturate L M) 24)

/-- The division-by-four loop: `x₀ = x`, `x_{i+1} = ⌊x_i / 4⌋`, stopped after `β` steps. -/
def divFourLoop (x : ℕ) : ℕ → ℕ
  | 0 => x
  | β + 1 => divFourLoop (x / 4) β

/-- Item 2: `β = σ_L(A⁽⁰⁾_ht M²⁴)`. -/
theorem cappedBound_eq (L M : ℕ) (hL : 1 ≤ L) : cappedBound L M = saturate L (A0 * M ^ 24) := by
  rw [cappedBound, NExpr.capped_eq L hL, NExpr.eval_eA, cappedPower_eq_saturate, saturate_pow,
    cappedMul_eq_saturate]
  exact saturate_mul L _ _

theorem cappedBound_le (L M : ℕ) (hL : 1 ≤ L) : cappedBound L M ≤ L + 1 := by
  rw [cappedBound_eq L M hL]; exact saturate_le_cap L _

/-- `x_β = ⌊x / 4^β⌋`. -/
theorem divFourLoop_eq (x β : ℕ) : divFourLoop x β = x / 4 ^ β := by
  induction β generalizing x with
  | zero => simp [divFourLoop]
  | succ β ih => rw [divFourLoop, ih, Nat.div_div_eq_div_mul, pow_succ', Nat.mul_comm 4]

/-- The saturated test: `⌊L / 4^(σ_L B)⌋ ≥ 1 ↔ 4^B ≤ L`. -/
theorem one_le_divFourLoop_saturate_iff (L B : ℕ) :
    1 ≤ divFourLoop L (saturate L B) ↔ 4 ^ B ≤ L := by
  rw [divFourLoop_eq, Nat.one_le_div_iff (by positivity)]
  by_cases hB : B ≤ L + 1
  · rw [saturate_eq_self L B hB]
  · rw [saturate_eq_cap L B (by omega)]
    have h1 : L + 1 < 4 ^ (L + 1) := Nat.lt_pow_self (by norm_num)
    have h2 : B < 4 ^ B := Nat.lt_pow_self (by norm_num)
    constructor <;> intro h <;> omega

/-- Item 3: the capped precision test computes `4^(A⁽⁰⁾_ht M²⁴) ≤ L`. -/
theorem precision_test_iff (L M : ℕ) (hL : 1 ≤ L) :
    1 ≤ divFourLoop L (cappedBound L M) ↔ 4 ^ (A0 * M ^ 24) ≤ L := by
  rw [cappedBound_eq L M hL]
  exact one_le_divFourLoop_saturate_iff L _

end ZInQ.Compiler.Precision
