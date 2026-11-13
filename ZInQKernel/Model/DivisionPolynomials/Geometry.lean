import ZInQKernel.Model.DivisionPolynomials.Classical

/-!
# Chord and tangent relations on `y² = x³ + Ax`

Two-point relations used by the multiplication-by-`n` argument: for affine points `Q`, `R`
with `x(Q) ≠ x(R)`, the sum and product of `x(Q + R)` and `x(Q - R)`, and their difference;
and the duplication formula `x(2Q) · 4y(Q)² = (x(Q)² - A)²`.
-/

namespace ZInQ.DivisionPolynomials

open WeierstrassCurve WeierstrassCurve.Affine
open ZInQ.Syntax (WA)

variable {F : Type*} [Field F] {A : F}

lemma WA_equation_iff {x y : F} : (WA A).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + A * x := by
  rw [Affine.equation_iff]; simp [WA]

lemma WA_negY (x y : F) : (WA A).toAffine.negY x y = -y := by
  simp [Affine.negY, WA]

variable [DecidableEq F]

lemma WA_add_X {x₁ y₁ x₂ y₂ x₃ y₃ : F} {h₁ : (WA A).toAffine.Nonsingular x₁ y₁}
    {h₂ : (WA A).toAffine.Nonsingular x₂ y₂} {h₃ : (WA A).toAffine.Nonsingular x₃ y₃}
    (hx : x₁ ≠ x₂) (h : Point.some _ _ h₁ + Point.some _ _ h₂ = Point.some x₃ y₃ h₃) :
    x₃ * (x₁ - x₂) ^ 2 = (y₁ - y₂) ^ 2 - (x₁ + x₂) * (x₁ - x₂) ^ 2 := by
  rw [Point.add_of_X_ne hx, Point.some.injEq] at h
  rw [← h.1, Affine.addX, Affine.slope_of_X_ne hx]
  have : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  simp only [WA, zero_mul, add_zero, sub_zero]
  field_simp
  ring

lemma exists_add_of_X_ne {x₁ y₁ x₂ y₂ : F} {h₁ : (WA A).toAffine.Nonsingular x₁ y₁}
    {h₂ : (WA A).toAffine.Nonsingular x₂ y₂} (hx : x₁ ≠ x₂) :
    ∃ x₃ y₃ h₃, Point.some _ _ h₁ + Point.some _ _ h₂ = Point.some x₃ y₃ h₃ :=
  ⟨_, _, _, Point.add_of_X_ne hx⟩

lemma exists_add_self_of_Y_ne (h2 : (2 : F) ≠ 0) {x₁ y₁ : F}
    {h₁ : (WA A).toAffine.Nonsingular x₁ y₁} (hy : y₁ ≠ 0) :
    ∃ x₃ y₃ h₃, Point.some _ _ h₁ + Point.some _ _ h₁ = Point.some x₃ y₃ h₃ := by
  have hy' : y₁ ≠ (WA A).toAffine.negY x₁ y₁ := by
    rw [WA_negY]; intro h'; apply hy
    have : 2 * y₁ = 0 := by linear_combination h'
    exact (mul_eq_zero.mp this).resolve_left h2
  exact ⟨_, _, _, Point.add_self_of_Y_ne hy'⟩

/-- The chord relations for `Q = (x₁, y₁)`, `R = (x₂, y₂)` with `x₁ ≠ x₂`,
`Q + R = (x₃, y₃)` and `Q - R = (x₄, y₄)`. -/
lemma chord_rel {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : F} {h₁ : (WA A).toAffine.Nonsingular x₁ y₁}
    {h₂ : (WA A).toAffine.Nonsingular x₂ y₂} {h₃ : (WA A).toAffine.Nonsingular x₃ y₃}
    {h₄ : (WA A).toAffine.Nonsingular x₄ y₄} (hx : x₁ ≠ x₂)
    (hadd : Point.some _ _ h₁ + Point.some _ _ h₂ = Point.some x₃ y₃ h₃)
    (hsub : Point.some _ _ h₁ - Point.some _ _ h₂ = Point.some x₄ y₄ h₄) :
    (x₃ + x₄) * (x₁ - x₂) ^ 2 = 2 * (x₁ * x₂ + A) * (x₁ + x₂) ∧
    x₃ * x₄ * (x₁ - x₂) ^ 2 = (x₁ * x₂ - A) ^ 2 ∧
    (x₃ - x₄) * (x₁ - x₂) ^ 2 = -4 * y₁ * y₂ := by
  rw [sub_eq_add_neg, Point.neg_some] at hsub
  have e3 := WA_add_X hx hadd
  have e4 := WA_add_X hx hsub
  rw [WA_negY] at e4
  have c1 := WA_equation_iff.mp h₁.1
  have c2 := WA_equation_iff.mp h₂.1
  have hD : (x₁ - x₂) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hx)
  refine ⟨?_, ?_, ?_⟩
  · linear_combination e3 + e4 + 2 * c1 + 2 * c2
  · refine mul_right_cancel₀ hD ?_
    linear_combination (x₄ * (x₁ - x₂) ^ 2) * e3 +
      ((y₁ - y₂) ^ 2 - (x₁ + x₂) * (x₁ - x₂) ^ 2) * e4 +
      (A * x₁ - x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - 2 * x₂ ^ 3 + y₁ ^ 2 - 2 * y₂ ^ 2) * c1 +
      (-2 * A * x₁ + A * x₂ - 4 * x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - x₂ ^ 3 + y₂ ^ 2) * c2
  · linear_combination e3 - e4

/-- The duplication relation `x(2Q) · 4y(Q)² = (x(Q)² - A)²` for `y(Q) ≠ 0`. -/
lemma dbl_rel (h2 : (2 : F) ≠ 0) {x₁ y₁ x₅ y₅ : F} {h₁ : (WA A).toAffine.Nonsingular x₁ y₁}
    {h₅ : (WA A).toAffine.Nonsingular x₅ y₅} (hy : y₁ ≠ 0)
    (h : Point.some _ _ h₁ + Point.some _ _ h₁ = Point.some x₅ y₅ h₅) :
    x₅ * (4 * y₁ ^ 2) = (x₁ ^ 2 - A) ^ 2 := by
  have hy' : y₁ ≠ (WA A).toAffine.negY x₁ y₁ := by
    rw [WA_negY]; intro h'; apply hy
    have : 2 * y₁ = 0 := by linear_combination h'
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [Point.add_self_of_Y_ne hy', Point.some.injEq] at h
  rw [← h.1, Affine.addX, Affine.slope_of_Y_ne rfl hy', WA_negY]
  have c1 := WA_equation_iff.mp h₁.1
  simp only [WA, mul_zero, zero_mul, add_zero, sub_zero]
  rw [show y₁ - -y₁ = 2 * y₁ by ring]
  field_simp
  linear_combination (-32 * x₁) * c1

end ZInQ.DivisionPolynomials
