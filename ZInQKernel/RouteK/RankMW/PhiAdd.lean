import ZInQKernel.Model.Descent.Kummer

/-!
# The two-isogeny `φ_b` is a homomorphism

For `E_b : y² = x³ + b x` and `b' = -4 b`, the two-isogeny `phi : E_b(K) → E_{b'}(K)` of
`Model/Descent/Kummer.lean` is additive.

Method: if `P₁, P₂, P₃ = -(P₁ + P₂)` lie on the line `y = ℓ x + ν` (all with `x ≠ 0`, so
`ν ≠ 0`), then their images `φ(Pᵢ) = (Xᵢ, Yᵢ)` lie on the line `Y = L X + N` with
`L = b/ν - ℓ`, `N = -ν - b ℓ²/ν` (a one-point identity, `mwPhi_line`), and
`X₁ + X₂ + X₃ = L²` (from Vieta's relations for `x₁, x₂, x₃`, `mwPhi_sum_sq`). The degenerate
cases (`O`, `(0,0)`, `P₂ = ±P₁`, `P₂ = ±(P₁ + (0,0))`) are handled separately using
`φ(-P) = -φ(P)` and `φ(P + (0,0)) = φ(P)`.
-/

namespace ZInQ.RouteK.Rank

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent

variable {K : Type*} [Field K]

/-! ### Pure algebra -/

/-- The image of a point of the line `y = ℓ x + ν` lies on `Y = L X + N`. -/
theorem mwPhi_line {b x y ℓ ν : K} (hx : x ≠ 0) (hν : ν ≠ 0) (hy : y = ℓ * x + ν)
    (he : y ^ 2 = x ^ 3 + b * x) :
    y * (b - x ^ 2) / x ^ 2 = (b / ν - ℓ) * (y ^ 2 / x ^ 2) + (-ν - b * ℓ ^ 2 / ν) := by
  subst hy
  field_simp
  linear_combination ℓ * ν * he

/-- `X₁ + X₂ + X₃ = L²` from Vieta's relations. -/
theorem mwPhi_sum_sq {b x₁ x₂ x₃ ℓ ν : K} (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0) (h₃ : x₃ ≠ 0)
    (hν : ν ≠ 0) (V1 : x₁ + x₂ + x₃ = ℓ ^ 2) (V2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = b - 2 * ℓ * ν)
    (V3 : x₁ * x₂ * x₃ = ν ^ 2) :
    (ℓ * x₁ + ν) ^ 2 / x₁ ^ 2 + (ℓ * x₂ + ν) ^ 2 / x₂ ^ 2 + (ℓ * x₃ + ν) ^ 2 / x₃ ^ 2 =
      (b / ν - ℓ) ^ 2 := by
  field_simp
  have hx3 : x₃ = ℓ ^ 2 - x₁ - x₂ := by linear_combination V1
  subst hx3
  have hb : b = x₁ * x₂ + (x₁ + x₂) * (ℓ ^ 2 - x₁ - x₂) + 2 * ℓ * ν := by linear_combination -V2
  subst hb
  linear_combination (-ℓ^6*x₁^3*x₂ - 2*ℓ^6*x₁^2*x₂^2 - ℓ^6*x₁*x₂^3 - 2*ℓ^5*ν*x₁^2*x₂ - 2*ℓ^5*ν*x₁*x₂^2 - ℓ^4*ν^2*x₁^2 - ℓ^4*ν^2*x₂^2 + 3*ℓ^4*x₁^4*x₂ + 7*ℓ^4*x₁^3*x₂^2 + 7*ℓ^4*x₁^2*x₂^3 + 3*ℓ^4*x₁*x₂^4 + 4*ℓ^3*ν*x₁^3*x₂ + 6*ℓ^3*ν*x₁^2*x₂^2 + 4*ℓ^3*ν*x₁*x₂^3 + 2*ℓ^2*ν^2*x₁^3 + 2*ℓ^2*ν^2*x₁^2*x₂ + 2*ℓ^2*ν^2*x₁*x₂^2 + 2*ℓ^2*ν^2*x₂^3 - 3*ℓ^2*x₁^5*x₂ - 8*ℓ^2*x₁^4*x₂^2 - 11*ℓ^2*x₁^3*x₂^3 - 8*ℓ^2*x₁^2*x₂^4 - 3*ℓ^2*x₁*x₂^5 - 2*ℓ*ν*x₁^4*x₂ - 4*ℓ*ν*x₁^3*x₂^2 - 4*ℓ*ν*x₁^2*x₂^3 - 2*ℓ*ν*x₁*x₂^4 - ν^2*x₁^4 - 2*ν^2*x₁^3*x₂ - 3*ν^2*x₁^2*x₂^2 - 2*ν^2*x₁*x₂^3 - ν^2*x₂^4 + x₁^6*x₂ + 3*x₁^5*x₂^2 + 5*x₁^4*x₂^3 + 5*x₁^3*x₂^4 + 3*x₁^2*x₂^5 + x₁*x₂^6) * V3

/-- Tangency of the image line at `φ(P)` (doubling case). -/
theorem mwPhi_tangent {b x y ℓ ν : K} (hx : x ≠ 0) (hν : ν ≠ 0) (hy : y = ℓ * x + ν)
    (he : y ^ 2 = x ^ 3 + b * x) (ht : 2 * y * ℓ = 3 * x ^ 2 + b) :
    (b / ν - ℓ) * (2 * (y * (b - x ^ 2) / x ^ 2)) = 3 * (y ^ 2 / x ^ 2) ^ 2 + -4 * b := by
  subst hy
  field_simp
  have hb : b = 2 * (ℓ * x + ν) * ℓ - 3 * x ^ 2 := by linear_combination -ht
  subst hb
  linear_combination (-8*ℓ^3*x^3 - 17*ℓ^2*ν*x^2 - 12*ℓ*ν^2*x + 12*ℓ*x^4 - 3*ν^3 + 6*ν*x^3) * he

/-! ### Addition on the target curve along a line -/

section Line

variable [DecidableEq K]

/-- Two points of `E_c` with distinct abscissas on the line `Y = L X + N` add up to the
reflection of the third point of that line. -/
theorem mwAdd_of_line {c X₁ Y₁ X₂ Y₂ X₃ Y₃ L N : K}
    (h₁ : (shortCurve c).toAffine.Nonsingular X₁ Y₁) (h₂ : (shortCurve c).toAffine.Nonsingular X₂ Y₂)
    (h₃ : (shortCurve c).toAffine.Nonsingular X₃ Y₃) (hX : X₁ ≠ X₂)
    (hl₁ : Y₁ = L * X₁ + N) (hl₂ : Y₂ = L * X₂ + N) (hl₃ : Y₃ = -(L * X₃ + N))
    (hs : X₁ + X₂ + X₃ = L ^ 2) :
    Point.some X₁ Y₁ h₁ + Point.some X₂ Y₂ h₂ = Point.some X₃ Y₃ h₃ := by
  rw [Point.add_of_X_ne hX]
  simp only [Point.some.injEq]
  have hL : (shortCurve c).toAffine.slope X₁ X₂ Y₁ Y₂ = L := by
    rw [Affine.slope_of_X_ne hX, div_eq_iff (sub_ne_zero.mpr hX)]
    linear_combination hl₁ - hl₂
  simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, shortCurve_a₁, shortCurve_a₂,
    shortCurve_a₃, hL, zero_mul, add_zero, sub_zero]
  constructor
  · linear_combination -hs
  · linear_combination -hl₁ + L * hs - hl₃

/-- Doubling along the tangent line `Y = L X + N`. -/
theorem mwDouble_of_line {c X₁ Y₁ X₃ Y₃ L N : K}
    (h₁ : (shortCurve c).toAffine.Nonsingular X₁ Y₁)
    (h₃ : (shortCurve c).toAffine.Nonsingular X₃ Y₃) (h2 : (2 : K) ≠ 0) (hY : Y₁ ≠ 0)
    (ht : L * (2 * Y₁) = 3 * X₁ ^ 2 + c)
    (hl₁ : Y₁ = L * X₁ + N) (hl₃ : Y₃ = -(L * X₃ + N))
    (hs : X₁ + X₁ + X₃ = L ^ 2) :
    Point.some X₁ Y₁ h₁ + Point.some X₁ Y₁ h₁ = Point.some X₃ Y₃ h₃ := by
  have hY' : Y₁ ≠ (shortCurve c).toAffine.negY X₁ Y₁ := by
    rw [shortCurve_negY]; intro h; apply hY
    have : (2 : K) * Y₁ = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [Point.add_self_of_Y_ne hY']
  simp only [Point.some.injEq]
  have hL : (shortCurve c).toAffine.slope X₁ X₁ Y₁ Y₁ = L := by
    rw [Affine.slope_of_Y_ne rfl hY']
    simp only [Affine.negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄,
      zero_mul, mul_zero, add_zero, sub_zero]
    rw [div_eq_iff (by
      intro h; apply hY
      have : (2 : K) * Y₁ = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left h2)]
    linear_combination -ht
  simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, shortCurve_a₁, shortCurve_a₂,
    shortCurve_a₃, hL, zero_mul, add_zero, sub_zero]
  constructor
  · linear_combination -hs
  · linear_combination -hl₁ + L * hs - hl₃

end Line

end ZInQ.RouteK.Rank
