import ZInQKernel.Model.DivisionPolynomials.Defs

/-!
# Agreement with the classical division polynomials

Blueprint: `syntax/division-polynomials-classical.md`.

For the Weierstrass curve `W_A : y² = x³ + Ax` (`a₁ = a₂ = a₃ = a₆ = 0`, `a₄ = A`), the
normalized division polynomials `f_n` are Mathlib's `preΨ'`, the bivariate `ψ_n` are Mathlib's
`Ψ`, and `ψ_n` agrees with Mathlib's bivariate division polynomial `ψ` modulo the curve
equation, hence at every point of `W_A`.
-/

namespace ZInQ.Syntax

open Polynomial
open scoped Polynomial.Bivariate

variable {R : Type*} [CommRing R]

/-- The Weierstrass curve `W_A : y² = x³ + Ax`. -/
def WA (A : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := 0

variable (A : R)

@[simp] lemma WA_a₁ : (WA A).a₁ = 0 := rfl
@[simp] lemma WA_a₂ : (WA A).a₂ = 0 := rfl
@[simp] lemma WA_a₃ : (WA A).a₃ = 0 := rfl
@[simp] lemma WA_a₄ : (WA A).a₄ = A := rfl
@[simp] lemma WA_a₆ : (WA A).a₆ = 0 := rfl

lemma WA_b₂ : (WA A).b₂ = 0 := by simp [WeierstrassCurve.b₂]
lemma WA_b₄ : (WA A).b₄ = 2 * A := by simp [WeierstrassCurve.b₄]
lemma WA_b₆ : (WA A).b₆ = 0 := by simp [WeierstrassCurve.b₆]
lemma WA_b₈ : (WA A).b₈ = -A ^ 2 := by simp [WeierstrassCurve.b₈]

lemma WA_Ψ₂Sq : (WA A).Ψ₂Sq = 4 * (X ^ 3 + C A * X) := by
  simp only [WeierstrassCurve.Ψ₂Sq, WA_b₂, WA_b₄, WA_b₆, map_zero, zero_mul, add_zero, map_mul]
  simp only [map_ofNat]
  ring

lemma WA_Ψ₂Sq_sq : (WA A).Ψ₂Sq ^ 2 = divD0 A := by
  rw [WA_Ψ₂Sq, divD0]; ring

lemma WA_Ψ₃ : (WA A).Ψ₃ = divF3 A := by
  simp only [WeierstrassCurve.Ψ₃, WA_b₂, WA_b₄, WA_b₆, WA_b₈, divF3, map_zero, map_mul, map_neg,
    map_pow, map_ofNat]
  ring

lemma WA_preΨ₄ : (WA A).preΨ₄ = divF4 A := by
  simp only [WeierstrassCurve.preΨ₄, WA_b₂, WA_b₄, WA_b₆, WA_b₈, divF4, map_zero, map_mul, map_neg,
    map_pow, map_ofNat, map_sub]
  ring

lemma WA_ψ₂ : (WA A).ψ₂ = 2 * Y := by
  simp only [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY, WeierstrassCurve.toAffine,
    WA_a₁, WA_a₃, map_zero, zero_mul, add_zero]
  simp only [map_ofNat]

/-- `f_n = preΨ_n` for `n ≥ 0`. -/
theorem normDiv_eq_preΨ' (n : ℕ) : normDiv A n = (WA A).preΨ' n := by
  rw [normDiv, WeierstrassCurve.preΨ', WA_Ψ₂Sq_sq, WA_Ψ₃, WA_preΨ₄]

/-- `ψ_n = Ψ_n` for `n ∈ ℤ`. -/
theorem divPsi_eq_Ψ (n : ℤ) : divPsi A n = (WA A).Ψ n := by
  rw [divPsi, WeierstrassCurve.Ψ, WeierstrassCurve.preΨ, WA_ψ₂, WA_Ψ₂Sq_sq, WA_Ψ₃, WA_preΨ₄]
  simp only [preNormEDS, normDiv, map_mul, map_intCast]
  ring

/-- `ψ_n` agrees with Mathlib's bivariate division polynomial `ψ_n` in the coordinate ring. -/
theorem mk_divPsi (n : ℤ) : WeierstrassCurve.Affine.CoordinateRing.mk (WA A) (divPsi A n) =
    WeierstrassCurve.Affine.CoordinateRing.mk (WA A) ((WA A).ψ n) := by
  rw [divPsi_eq_Ψ, WeierstrassCurve.Affine.CoordinateRing.mk_ψ]

/-- `ψ_n` and Mathlib's `ψ_n` take the same value at every point of `W_A`. -/
theorem psiEval_eq_evalEval_ψ (n : ℤ) {x y : R} (h : (WA A).toAffine.Equation x y) :
    psiEval A n x y = ((WA A).ψ n).evalEval x y := by
  have := congrArg (AdjoinRoot.evalEval h) (mk_divPsi A n)
  exact (AdjoinRoot.evalEval_mk h _).symm.trans (this.trans (AdjoinRoot.evalEval_mk h _))

end ZInQ.Syntax
