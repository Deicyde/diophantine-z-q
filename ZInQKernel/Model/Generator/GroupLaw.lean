import ZInQKernel.Model.Field.Codes

/-!
# The chord-and-tangent law on `E` in coordinates

The three cases of the group law of `E : y² = x³ - d² x` used by the membership and raw addition
templates: opposite points, distinct abscissas (chord) and doubling with nonzero ordinate
(tangent), together with the coordinates of codes.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

theorem genCurve_negY (x y : K0) : genCurve.toAffine.negY x y = -y :=
  shortCurve_negY _ x y

/-- The chord slope gives the sum: for `x₁ ≠ x₂`, with `m = (y₂ - y₁)/(x₂ - x₁)`,
`(x₁, y₁) + (x₂, y₂) = (m² - x₁ - x₂, m (x₁ - x₃) - y₁)`. -/
theorem genCurve_add_of_X_ne {x₁ y₁ x₂ y₂ : K0} (h₁ : genCurve.toAffine.Nonsingular x₁ y₁)
    (h₂ : genCurve.toAffine.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) (m : K0)
    (hm : (x₂ - x₁) * m = y₂ - y₁) :
    ∃ h, Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ =
      Point.some (m ^ 2 - x₁ - x₂) (m * (x₁ - (m ^ 2 - x₁ - x₂)) - y₁) h := by
  have hsl : genCurve.toAffine.slope x₁ x₂ y₁ y₂ = m := by
    rw [Affine.slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx)]
    linear_combination hm
  have hX0 : genCurve.toAffine.addX x₁ x₂ m = m ^ 2 - x₁ - x₂ := by
    rw [Affine.addX]; simp [genCurve]
  have hX : genCurve.toAffine.addX x₁ x₂ (genCurve.toAffine.slope x₁ x₂ y₁ y₂) =
      m ^ 2 - x₁ - x₂ := by rw [hsl, hX0]
  have hY : genCurve.toAffine.addY x₁ x₂ y₁ (genCurve.toAffine.slope x₁ x₂ y₁ y₂) =
      m * (x₁ - (m ^ 2 - x₁ - x₂)) - y₁ := by
    rw [Affine.addY, Affine.negAddY, hsl, hX0, genCurve_negY]; ring
  rw [Point.add_of_X_ne hx]
  refine ⟨by rw [← hY, ← hX]; exact nonsingular_add h₁ h₂ fun hxy => hx hxy.left, ?_⟩
  simp only [Point.some.injEq]
  exact ⟨hX, hY⟩

/-- The tangent slope gives the double: for `y ≠ 0`, with `2 y m = 3 x² - d²`,
`[2](x, y) = (m² - 2x, m (x - x₃) - y)`. -/
theorem genCurve_two_nsmul_of_Y_ne {x y : K0} (h : genCurve.toAffine.Nonsingular x y)
    (hy : y ≠ 0) (m : K0) (hm : 2 * y * m = 3 * x ^ 2 - genD ^ 2) :
    ∃ h', 2 • Point.some x y h =
      Point.some (m ^ 2 - x - x) (m * (x - (m ^ 2 - x - x)) - y) h' := by
  have hY : y ≠ genCurve.toAffine.negY x y := by
    rw [genCurve_negY]; intro h'; apply hy; linear_combination h' / 2
  have hsl : genCurve.toAffine.slope x x y y = m := by
    rw [Affine.slope_of_Y_ne rfl hY, genCurve_negY,
      div_eq_iff (by intro h'; apply hy; linear_combination h' / 2)]
    simp only [genCurve]
    linear_combination -hm
  have hX0 : genCurve.toAffine.addX x x m = m ^ 2 - x - x := by
    rw [Affine.addX]; simp [genCurve]
  have hX : genCurve.toAffine.addX x x (genCurve.toAffine.slope x x y y) = m ^ 2 - x - x := by
    rw [hsl, hX0]
  have hY' : genCurve.toAffine.addY x x y (genCurve.toAffine.slope x x y y) =
      m * (x - (m ^ 2 - x - x)) - y := by
    rw [Affine.addY, Affine.negAddY, hsl, hX0, genCurve_negY]; ring
  rw [two_nsmul, Point.add_self_of_Y_ne hY]
  refine ⟨by rw [← hY', ← hX]; exact nonsingular_add h h fun hxy => hY hxy.right, ?_⟩
  simp only [Point.some.injEq]
  exact ⟨hX, hY'⟩

/-- An affine point with zero ordinate is two-torsion. -/
theorem genCurve_two_nsmul_of_Y_eq_zero {x y : K0} (h : genCurve.toAffine.Nonsingular x y)
    (hy : y = 0) : 2 • Point.some x y h = 0 := by
  rw [two_nsmul]
  exact Point.add_self_of_Y_eq (by rw [genCurve_negY, hy, neg_zero])

/-! ### Coordinates of codes -/

/-- The abscissa `x = c₁ + c₂ s` encoded by `c ∈ ℚ⁵`. -/
def codeX (c : Fin 5 → ℚ) : K0 := ⟨c 1, c 2⟩

/-- The ordinate `y = c₃ + c₄ s` encoded by `c ∈ ℚ⁵`. -/
def codeY (c : Fin 5 → ℚ) : K0 := ⟨c 3, c 4⟩

@[simp] theorem codeX_pointCode_some {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    codeX (pointCode (.some x y h)) = x := rfl

@[simp] theorem codeY_pointCode_some {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    codeY (pointCode (.some x y h)) = y := rfl

@[simp] theorem pointCode_some_zero {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    pointCode (.some x y h) 0 = 0 := rfl

/-- A code with first coordinate `0` is the code of an affine point exactly when its abscissa
and ordinate are those of the point. -/
theorem eq_pointCode_some_iff {c : Fin 5 → ℚ} {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    c = pointCode (.some x y h) ↔ c 0 = 0 ∧ codeX c = x ∧ codeY c = y := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, rfl, rfl⟩
    funext i
    fin_cases i <;> simp [h0, codeX, codeY]

theorem pointCode_zero_apply_zero : pointCode 0 0 = 1 := rfl

/-- The code of `O` has first coordinate `1`, so differs from every code with first
coordinate `0`. -/
theorem ne_pointCode_zero_of_apply_zero {c : Fin 5 → ℚ} (h : c 0 = 0) : c ≠ pointCode 0 := by
  rintro rfl; exact one_ne_zero h

end ZInQ
