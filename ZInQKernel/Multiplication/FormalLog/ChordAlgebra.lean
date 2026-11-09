import ZInQKernel.Multiplication.Local.FormalGroup

/-!
# `z(P₁ + P₂)` from a line through `P₁`, `P₂`

In the coordinates `z = -x/y`, `ω = -1/y` of `y² = x³ + A x`, let `ω = Λ z + N` be the line
through two affine points `P₁ = (x₁, y₁)`, `P₂ = (x₂, y₂)` with `y₁ y₂ ≠ 0` (the tangent if
`P₁ = P₂`), and suppose `P₁ + P₂` is an affine point with `y ≠ 0`. Then
`z(P₁ + P₂) = z₁ + z₂ + 2AΛN/(1 + AΛ²)` (`zCoord_add_of_line`): in the `(x, y)`-plane the line
is `y = (Λ/N) x - 1/N`, and Vieta's relations for the three abscissas (`vieta_shortCurve`,
`sum_t_identity`) give the sum of the `z`-coordinates.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K]

/-- **The chord formula.** -/
theorem zCoord_add_of_line {A x₁ y₁ x₂ y₂ Λ : K} (h2 : (2 : K) ≠ 0)
    (h₁ : (shortCurve A).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Nonsingular x₂ y₂) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hne : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ ≠ 0)
    (hy₃ : ∀ x y (h : (shortCurve A).toAffine.Nonsingular x y),
      Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x y h → y ≠ 0)
    (hD : 1 + A * Λ ^ 2 ≠ 0)
    (hchord : Λ * (-x₂ / y₂ - -x₁ / y₁) = -1 / y₂ - -1 / y₁)
    (htan : x₁ = x₂ → y₁ = y₂ →
      Λ * (1 - 2 * A * (-x₁ / y₁) * (-1 / y₁)) = 3 * (-x₁ / y₁) ^ 2 + A * (-1 / y₁) ^ 2) :
    zCoord (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) =
      -x₁ / y₁ + -x₂ / y₂ + 2 * A * Λ * (-1 / y₁ - Λ * (-x₁ / y₁)) / (1 + A * Λ ^ 2) := by
  have e₁ := (shortCurve_equation_iff A x₁ y₁).mp h₁.1
  have e₂ := (shortCurve_equation_iff A x₂ y₂).mp h₂.1
  have hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂) :=
    fun h => hne (Point.add_of_Y_eq h.1 h.2)
  have hsame : x₁ = x₂ → y₁ = y₂ := fun hx => by
    rcases Y_eq_of_X_eq h₁.1 h₂.1 hx with h | h
    · exact h
    · exact absurd ⟨hx, h⟩ hxy
  set N := -1 / y₁ - Λ * (-x₁ / y₁) with hN
  have hl₁ : N * y₁ = Λ * x₁ - 1 := by rw [hN]; field_simp; ring
  have hl₂ : N * y₂ = Λ * x₂ - 1 := by
    have : N = -1 / y₂ - Λ * (-x₂ / y₂) := by rw [hN]; linear_combination hchord
    rw [this]; field_simp; ring
  -- the tangent relation without denominators
  have htan' : x₁ = x₂ → y₁ = y₂ → Λ * (y₁ ^ 2 - 2 * A * x₁) = 3 * x₁ ^ 2 + A := by
    intro hx hy
    have h := htan hx hy
    have e : Λ * (1 - 2 * A * (-x₁ / y₁) * (-1 / y₁)) - (3 * (-x₁ / y₁) ^ 2 + A * (-1 / y₁) ^ 2) =
        (Λ * (y₁ ^ 2 - 2 * A * x₁) - (3 * x₁ ^ 2 + A)) / y₁ ^ 2 := by
      field_simp
    rw [h, sub_self, eq_comm, div_eq_zero_iff] at e
    exact sub_eq_zero.mp (e.resolve_right (pow_ne_zero 2 hy₁))
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hl₁ hl₂
    by_cases hx : x₁ = x₂
    · have hy := hsame hx
      have ht := htan' hx hy
      have key : 2 * (x₁ ^ 2 + A) = 0 := by
        linear_combination -ht + Λ * e₁ + (A - x₁ ^ 2) * hl₁
      have hx0 : x₁ ≠ 0 := by rintro rfl; simp at hl₁
      apply hD
      have hsq : x₁ ^ 2 + A = 0 := (mul_eq_zero.mp key).resolve_left h2
      have : (1 + A * Λ ^ 2) * x₁ ^ 2 = 0 := by linear_combination hsq - (A * (Λ * x₁ + 1)) * hl₁
      exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero 2 hx0)
    · apply hx
      have hΛ : Λ ≠ 0 := by rintro rfl; simp at hl₁
      have : Λ * (x₁ - x₂) = 0 := by linear_combination hl₂ - hl₁
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hΛ)
  have hslope : (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = Λ / N := by
    by_cases hx : x₁ = x₂
    · have hy := hsame hx
      have ht := htan' hx hy
      subst hx hy
      have hy' : y₁ ≠ (shortCurve A).toAffine.negY x₁ y₁ := fun h => hxy ⟨rfl, h⟩
      rw [slope_of_Y_ne rfl hy']
      simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₄, shortCurve_negY]
      have h2y : y₁ - -y₁ ≠ 0 := by
        rw [sub_neg_eq_add, ← two_mul]; exact mul_ne_zero h2 hy₁
      rw [div_eq_div_iff h2y hN0]
      have : ((3 * x₁ ^ 2 + 2 * 0 * x₁ + A - 0 * y₁) * N - Λ * (y₁ - -y₁)) * y₁ = 0 := by
        linear_combination (3 * x₁ ^ 2 + A) * hl₁ + ht - 3 * Λ * e₁
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hy₁)
    · rw [slope_of_X_ne hx, div_eq_div_iff (sub_ne_zero.mpr hx) hN0]
      linear_combination hl₁ - hl₂
  rw [Point.add_some hxy, zCoord_some]
  have hy₃' := hy₃ _ _ (nonsingular_add h₁ h₂ hxy) (Point.add_some hxy)
  have eX : (shortCurve A).toAffine.addX x₁ x₂ ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂) =
      (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂ := by
    rw [Affine.addX, shortCurve_a₁, shortCurve_a₂]; ring
  have eY : (shortCurve A).toAffine.addY x₁ x₂ y₁ ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂) =
      -((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ *
        ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂) +
          (y₁ - (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ * x₁)) := by
    rw [Affine.addY, Affine.negAddY, eX, shortCurve_negY]; ring
  rw [eY] at hy₃'
  rw [eX, eY]
  have V := vieta_shortCurve h₁.1 h₂.1 hxy (ℓ := Λ / N) hslope
  rw [hslope] at hy₃' ⊢
  have hc : y₁ - Λ / N * x₁ = -1 / N := by field_simp; linear_combination hl₁
  rw [hc] at V hy₃' ⊢
  obtain ⟨V2, V3⟩ := V
  have hD' : A * (Λ / N) ^ 2 + (-1 / N) ^ 2 ≠ 0 := by
    have : A * (Λ / N) ^ 2 + (-1 / N) ^ 2 = (1 + A * Λ ^ 2) / N ^ 2 := by field_simp; ring
    rw [this]; exact div_ne_zero hD (pow_ne_zero 2 hN0)
  have hid := sum_t_identity (A := A) (x₁ := x₁) (x₂ := x₂) (x₃ := (Λ / N) ^ 2 - x₁ - x₂)
    (y₃ := -(Λ / N * ((Λ / N) ^ 2 - x₁ - x₂) + -1 / N)) (by ring) V2 V3
    (by field_simp; linear_combination hl₁) (by field_simp; linear_combination hl₂)
    (by ring) hy₁ hy₂ hy₃' hD'
  have e2 : 2 * A * (Λ / N) / (A * (Λ / N) ^ 2 + (-1 / N) ^ 2) =
      2 * A * Λ * N / (1 + A * Λ ^ 2) := by
    rw [div_eq_div_iff hD' hD]; field_simp; ring
  rw [e2] at hid
  linear_combination hid

end ZInQ.Mult
