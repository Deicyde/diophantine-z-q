import ZInQKernel.Model.Field

/-!
# The translates of `R` by two-torsion

Blueprint: `model/heights/r-torsion-translates.md`.

On `C : y² = x³ - δ² x` with `R = (1 + s, 2 s)`, the chord rule with distinct abscissas gives
`x(R + (0,0)) = 23 - 17 s`, `x(R + (δ,0)) = 2 + 4 s` and `x(R + (-δ,0)) = (5 - 4 s)/2`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

/-- The chord rule on `C`: for distinct abscissas the sum of two affine points is the affine
point with abscissa `λ² - x₁ - x₂`, `λ = (y₁ - y₂)/(x₁ - x₂)`. -/
theorem curveC_add_of_X_ne {x₁ y₁ x₂ y₂ : K0} (h₁ : curveC.toAffine.Nonsingular x₁ y₁)
    (h₂ : curveC.toAffine.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) {x₃ : K0}
    (h₃ : ((y₁ - y₂) / (x₁ - x₂)) ^ 2 - x₁ - x₂ = x₃) :
    ∃ y h, Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y h := by
  rw [Point.add_of_X_ne hx]
  have hX : curveC.toAffine.addX x₁ x₂ (curveC.toAffine.slope x₁ x₂ y₁ y₂) = x₃ := by
    rw [Affine.slope_of_X_ne hx, Affine.addX, ← h₃]
    simp [curveC]
  refine ⟨_, hX ▸ nonsingular_add h₁ h₂ fun hxy => hx hxy.left, ?_⟩
  simp only [Point.some.injEq]
  exact ⟨hX, trivial⟩

theorem pointR_eq : pointR = Point.some epsilon (2 * sqrt2)
    (equation_iff_nonsingular.mp pointR_equation) := rfl

/-- `x(R + (0,0)) = 23 - 17 s`. -/
theorem x_pointR_add_cT0 :
    ∃ y h, pointR + cT0 = Point.some (⟨23, -17⟩ : K0) y h := by
  have hne : epsilon - 0 ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; norm_num [epsilon] at this
  refine curveC_add_of_X_ne _ _ (sub_ne_zero.mp hne) ?_
  have : (2 * sqrt2 - 0) / (epsilon - 0) = ⟨4, -2⟩ := by
    rw [div_eq_iff hne]; ext <;> norm_num [epsilon, sqrt2]
  rw [this]; ext <;> norm_num [epsilon, pow_two]

/-- `x(R + (δ,0)) = 2 + 4 s`. -/
theorem x_pointR_add_cTdelta :
    ∃ y h, pointR + cTdelta = Point.some (⟨2, 4⟩ : K0) y h := by
  have hne : epsilon - delta ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; norm_num [epsilon, delta] at this
  refine curveC_add_of_X_ne _ _ (sub_ne_zero.mp hne) ?_
  have : (2 * sqrt2 - 0) / (epsilon - delta) = ⟨2, 1⟩ := by
    rw [div_eq_iff hne]; ext <;> norm_num [epsilon, delta, sqrt2]
  rw [this]; ext <;> norm_num [epsilon, delta, pow_two]

/-- `x(R + (-δ,0)) = (5 - 4 s)/2`. -/
theorem x_pointR_add_cTnegdelta :
    ∃ y h, pointR + cTnegdelta = Point.some (⟨5 / 2, -2⟩ : K0) y h := by
  have hne : epsilon - -delta ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; norm_num [epsilon, delta] at this
  refine curveC_add_of_X_ne _ _ (sub_ne_zero.mp hne) ?_
  have : (2 * sqrt2 - 0) / (epsilon - -delta) = ⟨0, 1 / 2⟩ := by
    rw [div_eq_iff hne]; ext <;> norm_num [epsilon, delta, sqrt2]
  have h : (⟨0, 1 / 2⟩ : K0) ^ 2 = ⟨1 / 2, 0⟩ := by
    rw [pow_two, K0.mk_mul_mk']; norm_num
  rw [this, h]
  ext
  · simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.re_neg, epsilon, delta]; norm_num
  · simp only [QuadraticAlgebra.im_sub, QuadraticAlgebra.im_neg, epsilon, delta]; norm_num

/-- `(5 - 4 s)/2 = 5/2 - 2 s`. -/
theorem five_sub_four_sqrt2_div_two : (5 - 4 * sqrt2) / 2 = (⟨5 / 2, -2⟩ : K0) := by
  rw [div_eq_iff two_ne_zero]; ext <;> norm_num [sqrt2]

end ZInQ
