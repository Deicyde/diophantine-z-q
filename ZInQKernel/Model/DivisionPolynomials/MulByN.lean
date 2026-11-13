import ZInQKernel.Model.DivisionPolynomials.Multiples
import ZInQKernel.Hypotheses.MordellWeil

/-!
# The multiplication-by-`n` formulas for `E` over `K₀`

Blueprints: `syntax/division-polynomial-multiplication.md` (the proposition, proved here as a
theorem) and `model/field/division-polynomial-multiples.md` (the theorem, for `E` and for
`y² = x³ + Ax` over any field of characteristic zero).
-/

namespace ZInQ

open WeierstrassCurve
open ZInQ.Syntax (WA psiEval)

/-- The coefficient `A = -d² = -11243 + 7950 s` of `E : y² = x³ + Ax`. -/
noncomputable def genA : K0 := -genD ^ 2

lemma genA_eq : genA = ⟨-11243, 7950⟩ := by
  ext <;> simp [genA, genD, sq] <;> norm_num

lemma genCurve_eq_WA : genCurve = WA genA := rfl

/-- **The multiplication-by-`n` formulas** for `E : y² = x³ - d²x` over `K₀`: for every affine
point `P = (x, y) ∈ E(K₀)` and every integer `n ≠ 0`, `[n]P = O` iff `ψ_n(x, y) = 0`, and if
`[n]P ≠ O` then `x([n]P) = x - ψ_{n+1}ψ_{n-1}/ψ_n²` and `y([n]P) = ψ_{2n}/(2ψ_n⁴)`, where `ψ_k`
are the division polynomials of `y² = x³ + Ax` with `A = -d²`. -/
def DivisionPolynomialMultiplication : Prop :=
  ∀ (x y : K0) (h : genCurve.toAffine.Nonsingular x y) (n : ℤ), n ≠ 0 →
    (n • Affine.Point.some x y h = 0 ↔ psiEval genA n x y = 0) ∧
    (n • Affine.Point.some x y h ≠ 0 →
      ∃ h' : genCurve.toAffine.Nonsingular
          (x - psiEval genA (n + 1) x y * psiEval genA (n - 1) x y / psiEval genA n x y ^ 2)
          (psiEval genA (2 * n) x y / (2 * psiEval genA n x y ^ 4)),
        n • Affine.Point.some x y h = Affine.Point.some _ _ h')

/-- **Division polynomials compute multiples** on `y² = x³ + Ax` over any field of
characteristic zero, for every integer `n` (for `n = 0` both parts are trivial). -/
theorem mulByN_formulas_of_charZero {K : Type*} [Field K] [CharZero K] [DecidableEq K] (A : K)
    {x y : K} (h : (WA A).toAffine.Nonsingular x y) (n : ℤ) :
    (n • Affine.Point.some x y h = 0 ↔ psiEval A n x y = 0) ∧
    (n • Affine.Point.some x y h ≠ 0 →
      ∃ h' : (WA A).toAffine.Nonsingular
          (x - psiEval A (n + 1) x y * psiEval A (n - 1) x y / psiEval A n x y ^ 2)
          (psiEval A (2 * n) x y / (2 * psiEval A n x y ^ 4)),
        n • Affine.Point.some x y h = Affine.Point.some _ _ h') := by
  obtain ⟨h1, h2⟩ := DivisionPolynomials.zsmul_spec h n
  exact ⟨h1, fun hn => h2 (fun h0 => hn (h1.mpr h0))⟩

/-- **Division polynomials compute multiples** for `E` over `K₀`. -/
theorem mulByN_formulas : DivisionPolynomialMultiplication := fun _ _ h n _ =>
  mulByN_formulas_of_charZero genA h n

end ZInQ
