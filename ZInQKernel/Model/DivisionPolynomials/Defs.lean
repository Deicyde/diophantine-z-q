import Mathlib

/-!
# Normalized division polynomials of `y² = x³ + A x`

Blueprint: `syntax/division-polynomials.md`.

The normalized division polynomials `f_n ∈ R[x]` (`normDiv`), the bivariate division
polynomials `ψ_n ∈ R[x, y]` (`divPsi`), and the component polynomials `Ψ_{n,c}` of `ψ_n`
over `ℤ[x₀, x₁, y₀, y₁][s]/(s² - 2)` with `A = -11243 + 7950 s` (`psiComponent`).

`normDiv A` is Mathlib's normalized elliptic divisibility sequence `preNormEDS'` with parameter
`D₀ = 16(x³ + Ax)²` and initial values `0, 1, 1, f₃, f₄`; its defining recursion is exactly the
recursion of the manuscript, see `normDiv_even` and `normDiv_odd`.
-/

namespace ZInQ.Syntax

open Polynomial
open scoped Polynomial.Bivariate

variable {R : Type*} [CommRing R]

/-- The parameter `D₀ = 16(x³ + Ax)²` of the odd recurrence. -/
noncomputable def divD0 (A : R) : R[X] := 16 * (X ^ 3 + C A * X) ^ 2

/-- `f₃ = 3x⁴ + 6Ax² - A²`. -/
noncomputable def divF3 (A : R) : R[X] := 3 * X ^ 4 + 6 * C A * X ^ 2 - C A ^ 2

/-- `f₄ = 2(x⁶ + 5Ax⁴ - 5A²x² - A³)`. -/
noncomputable def divF4 (A : R) : R[X] :=
  2 * (X ^ 6 + 5 * C A * X ^ 4 - 5 * C A ^ 2 * X ^ 2 - C A ^ 3)

/-- The normalized division polynomials `f_n ∈ R[x]` of `y² = x³ + Ax`, `n ≥ 0`. -/
noncomputable def normDiv (A : R) (n : ℕ) : R[X] :=
  preNormEDS' (divD0 A) (divF3 A) (divF4 A) n

section normDiv

variable (A : R)

@[simp] lemma normDiv_zero : normDiv A 0 = 0 := preNormEDS'_zero ..
@[simp] lemma normDiv_one : normDiv A 1 = 1 := preNormEDS'_one ..
@[simp] lemma normDiv_two : normDiv A 2 = 1 := preNormEDS'_two ..
lemma normDiv_three : normDiv A 3 = 3 * X ^ 4 + 6 * C A * X ^ 2 - C A ^ 2 := preNormEDS'_three ..
lemma normDiv_four : normDiv A 4 = 2 * (X ^ 6 + 5 * C A * X ^ 4 - 5 * C A ^ 2 * X ^ 2 - C A ^ 3) :=
  preNormEDS'_four ..

/-- The even recurrence `f_{2m} = f_m (f_{m+2} f_{m-1}² - f_{m-2} f_{m+1}²)` for `m ≥ 3`. -/
lemma normDiv_even {m : ℕ} (hm : 3 ≤ m) : normDiv A (2 * m) =
    normDiv A m * (normDiv A (m + 2) * normDiv A (m - 1) ^ 2 -
      normDiv A (m - 2) * normDiv A (m + 1) ^ 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [normDiv, preNormEDS'_even, show k + 3 + 2 = k + 5 by ring,
    show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 + 1 = k + 4 by ring]
  ring

/-- The odd recurrence `f_{2m+1} = D₀ L - R_m` (`m` even), `L - D₀ R_m` (`m` odd) for `m ≥ 2`,
where `L = f_{m+2} f_m³`, `R_m = f_{m-1} f_{m+1}³` and `D₀ = 16(x³ + Ax)²`. -/
lemma normDiv_odd {m : ℕ} (hm : 2 ≤ m) : normDiv A (2 * m + 1) =
    if Even m then
      divD0 A * (normDiv A (m + 2) * normDiv A m ^ 3) - normDiv A (m - 1) * normDiv A (m + 1) ^ 3
    else
      normDiv A (m + 2) * normDiv A m ^ 3 - divD0 A * (normDiv A (m - 1) * normDiv A (m + 1) ^ 3)
    := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have hk : Even (k + 2) ↔ Even k := by simp [Nat.even_add]
  simp only [normDiv, preNormEDS'_odd, show k + 2 + 2 = k + 4 by ring,
    show k + 2 - 1 = k + 1 by omega, show k + 2 + 1 = k + 3 by ring, hk]
  split_ifs <;> ring

end normDiv

/-- The division polynomials `ψ_n ∈ R[x, y]`, `n ∈ ℤ`, of `y² = x³ + Ax`:
`ψ_n = f_n` for odd `n ≥ 0`, `ψ_n = 2y f_n` for even `n ≥ 0`, and `ψ_{-n} = -ψ_n`. -/
noncomputable def divPsi (A : R) (n : ℤ) : R[X][Y] :=
  (n.sign : R[X][Y]) * (C (normDiv A n.natAbs) * if Even n then 2 * Y else 1)

section divPsi

variable (A : R)

lemma divPsi_ofNat (n : ℕ) :
    divPsi A n = C (normDiv A n) * if Even n then 2 * Y else 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [divPsi]
  · simp [divPsi, Int.sign_natCast_of_ne_zero hn.ne', Int.even_coe_nat]

lemma divPsi_of_even {n : ℕ} (hn : Even n) : divPsi A n = 2 * Y * C (normDiv A n) := by
  rw [divPsi_ofNat, ite_eq_left_iff.mpr (fun h => absurd hn h), mul_comm]

lemma divPsi_of_odd {n : ℕ} (hn : ¬Even n) : divPsi A n = C (normDiv A n) := by
  rw [divPsi_ofNat, ite_eq_right_iff.mpr (fun h => absurd h hn), mul_one]

lemma divPsi_neg (n : ℤ) : divPsi A (-n) = -divPsi A n := by
  simp only [divPsi, Int.sign_neg, even_neg, Int.natAbs_neg, Int.cast_neg]
  ring

end divPsi

/-- The value `ψ_n(x, y)` of the division polynomial `ψ_n` at a point `(x, y)`. -/
noncomputable def psiEval (A : R) (n : ℤ) (x y : R) : R :=
  (divPsi A n).evalEval x y

lemma evalEval_two (x y : R) : (2 : R[X][Y]).evalEval x y = 2 := by
  simpa using evalEval_natCast x y 2

lemma psiEval_eq (A : R) (n : ℤ) (x y : R) : psiEval A n x y =
    n.sign * ((normDiv A n.natAbs).eval x * if Even n then 2 * y else 1) := by
  simp only [psiEval, divPsi, evalEval_mul, evalEval_intCast, evalEval_C]
  split_ifs <;> simp [evalEval_mul, evalEval_X, evalEval_two]

/-! ### Components over `ℤ[x₀, x₁, y₀, y₁][s]/(s² - 2)` -/

/-- The ring `ℤ[x₀, x₁, y₀, y₁][s]/(s² - 2)` of pairs over `ℤ[x₀, x₁, y₀, y₁]`. -/
abbrev ComponentRing : Type := QuadraticAlgebra (MvPolynomial (Fin 4) ℤ) 2 0

/-- The coefficient `A = -d² = -11243 + 7950 s`. -/
noncomputable def componentA : ComponentRing := ⟨-11243, 7950⟩

/-- The component polynomial `Ψ_{n,c} ∈ ℤ[x₀, x₁, y₀, y₁]`: the coefficient of `s^c` in
`ψ_n(x₀ + x₁ s, y₀ + y₁ s)` for `A = -11243 + 7950 s`. -/
noncomputable def psiComponent (n : ℤ) (c : Fin 2) : MvPolynomial (Fin 4) ℤ :=
  let v : ComponentRing := psiEval componentA n ⟨.X 0, .X 1⟩ ⟨.X 2, .X 3⟩
  ![v.re, v.im] c

end ZInQ.Syntax
