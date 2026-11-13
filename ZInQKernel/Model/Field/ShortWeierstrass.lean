import Mathlib

/-!
# Short Weierstrass curves `y² = x³ + A x`

Generic facts about the curves `E_A : y² = x³ + A x` over a field `F` used for the generator
curve `E = E_{-d²}` and the curve `C = E_{-δ²}`:

* the curve equation and the discriminant `Δ = -64 A³`;
* the points of order dividing two are `O` and the affine points with `y = 0`;
* for `u ≠ 0` and `B = u⁴ A`, the scaling `(x, y) ↦ (u² x, u³ y)` is an isomorphism of groups
  `E_A(F) ≃+ E_B(F)`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F]

/-- The short Weierstrass curve `y² = x³ + A x`. -/
def shortCurve (A : F) : WeierstrassCurve F where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := 0

@[simp] theorem shortCurve_a₁ (A : F) : (shortCurve A).a₁ = 0 := rfl
@[simp] theorem shortCurve_a₂ (A : F) : (shortCurve A).a₂ = 0 := rfl
@[simp] theorem shortCurve_a₃ (A : F) : (shortCurve A).a₃ = 0 := rfl
@[simp] theorem shortCurve_a₄ (A : F) : (shortCurve A).a₄ = A := rfl
@[simp] theorem shortCurve_a₆ (A : F) : (shortCurve A).a₆ = 0 := rfl

theorem shortCurve_equation_iff (A x y : F) :
    (shortCurve A).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + A * x := by
  rw [Affine.equation_iff]; simp

theorem shortCurve_Δ (A : F) : (shortCurve A).Δ = -64 * A ^ 3 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, shortCurve]
  ring

theorem shortCurve_isElliptic [NeZero (2 : F)] {A : F} (hA : A ≠ 0) :
    (shortCurve A).IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [shortCurve_Δ]
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have h64 : (64 : F) = 2 ^ 6 := by norm_num
  rw [h64]
  exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ h2)) (pow_ne_zero _ hA)

theorem shortCurve_negY (A x y : F) : (shortCurve A).toAffine.negY x y = -y := by
  simp [Affine.negY]

section DecEq

variable [DecidableEq F]

/-- In any Weierstrass curve, an affine point has order dividing two iff `y = negY x y`. -/
theorem two_nsmul_some_eq_zero_iff {W : WeierstrassCurve F} {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    2 • Point.some x y h = 0 ↔ y = W.toAffine.negY x y := by
  rw [two_nsmul]
  constructor
  · intro h'
    by_contra hne
    rw [Point.add_self_of_Y_ne hne] at h'
    exact Point.some_ne_zero _ h'
  · intro hy
    exact Point.add_self_of_Y_eq hy

/-- On `y² = x³ + A x` (with `2 ≠ 0`), an affine point has order dividing two iff `y = 0`. -/
theorem shortCurve_two_nsmul_some_eq_zero_iff [NeZero (2 : F)] {A x y : F}
    (h : (shortCurve A).toAffine.Nonsingular x y) :
    2 • Point.some x y h = 0 ↔ y = 0 := by
  rw [two_nsmul_some_eq_zero_iff, shortCurve_negY]
  constructor
  · intro hy
    have : (2 : F) * y = 0 := by linear_combination hy
    exact (mul_eq_zero.mp this).resolve_left (NeZero.ne 2)
  · intro hy; rw [hy, neg_zero]

end DecEq

/-! ### Scaling `(x, y) ↦ (u² x, u³ y)` -/

section Scale

variable {A B u : F}

theorem shortCurve_equation_scale (hu : u ≠ 0) (hB : B = u ^ 4 * A) (x y : F) :
    (shortCurve B).toAffine.Equation (u ^ 2 * x) (u ^ 3 * y) ↔
      (shortCurve A).toAffine.Equation x y := by
  rw [shortCurve_equation_iff, shortCurve_equation_iff, hB]
  have h6 : u ^ 6 ≠ 0 := pow_ne_zero 6 hu
  constructor
  · intro h
    apply mul_left_cancel₀ h6
    linear_combination h
  · intro h
    linear_combination u ^ 6 * h

variable [(shortCurve A).IsElliptic] [(shortCurve B).IsElliptic]

theorem shortCurve_nonsingular_scale (hu : u ≠ 0) (hB : B = u ^ 4 * A) {x y : F}
    (h : (shortCurve A).toAffine.Nonsingular x y) :
    (shortCurve B).toAffine.Nonsingular (u ^ 2 * x) (u ^ 3 * y) :=
  equation_iff_nonsingular.mp
    ((shortCurve_equation_scale hu hB x y).mpr (equation_iff_nonsingular.mpr h))

/-- The scaling map on points, `O ↦ O`, `(x, y) ↦ (u² x, u³ y)`. -/
def scalePoint (hu : u ≠ 0) (hB : B = u ^ 4 * A) :
    (shortCurve A).toAffine.Point → (shortCurve B).toAffine.Point
  | 0 => 0
  | .some _ _ h => .some _ _ (shortCurve_nonsingular_scale hu hB h)

@[simp] theorem scalePoint_zero (hu : u ≠ 0) (hB : B = u ^ 4 * A) :
    scalePoint hu hB 0 = 0 := rfl

@[simp] theorem scalePoint_some (hu : u ≠ 0) (hB : B = u ^ 4 * A) {x y : F}
    (h : (shortCurve A).toAffine.Nonsingular x y) :
    scalePoint hu hB (.some x y h) = .some _ _ (shortCurve_nonsingular_scale hu hB h) := rfl

variable [DecidableEq F]

theorem shortCurve_slope_scale (hu : u ≠ 0) (A B : F) (x₁ x₂ y₁ y₂ : F) (hB : B = u ^ 4 * A) :
    (shortCurve B).toAffine.slope (u ^ 2 * x₁) (u ^ 2 * x₂) (u ^ 3 * y₁) (u ^ 3 * y₂) =
      u * (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ := by
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have hu3 : u ^ 3 ≠ 0 := pow_ne_zero 3 hu
  simp only [Affine.slope, shortCurve_negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₄,
    mul_right_inj' hu2, hB]
  by_cases hx : x₁ = x₂
  · simp only [hx, ite_true]
    by_cases hy : y₁ = -y₂
    · have : u ^ 3 * y₁ = -(u ^ 3 * y₂) := by rw [hy]; ring
      simp [hy]
    · have : ¬ u ^ 3 * y₁ = -(u ^ 3 * y₂) := by
        intro h; apply hy; apply mul_left_cancel₀ hu3; linear_combination h
      simp only [hy, this, ite_false]
      by_cases hy0 : y₁ - -y₁ = 0
      · have : u ^ 3 * y₁ - -(u ^ 3 * y₁) = 0 := by linear_combination u ^ 3 * hy0
        simp [hy0, this]
      · have : u ^ 3 * y₁ - -(u ^ 3 * y₁) ≠ 0 := by
          intro h; apply hy0; apply mul_left_cancel₀ hu3; linear_combination h
        field_simp
        ring
  · simp only [hx, ite_false]
    have h1 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have h2 : u ^ 2 * x₁ - u ^ 2 * x₂ ≠ 0 := by
      rw [← mul_sub]; exact mul_ne_zero hu2 h1
    field_simp

theorem scalePoint_add (hu : u ≠ 0) (hB : B = u ^ 4 * A) (P Q : (shortCurve A).toAffine.Point) :
    scalePoint hu hB (P + Q) = scalePoint hu hB P + scalePoint hu hB Q := by
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have hu3 : u ^ 3 ≠ 0 := pow_ne_zero 3 hu
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂
  · have hxy' : u ^ 2 * x₁ = u ^ 2 * x₂ ∧
        u ^ 3 * y₁ = (shortCurve B).toAffine.negY (u ^ 2 * x₂) (u ^ 3 * y₂) := by
      rw [shortCurve_negY] at hxy ⊢
      exact ⟨by rw [hxy.1], by rw [hxy.2]; ring⟩
    rw [Point.add_of_Y_eq hxy.1 hxy.2, scalePoint_some, scalePoint_some,
      Point.add_of_Y_eq hxy'.1 hxy'.2, scalePoint_zero]
  · have hxy' : ¬ (u ^ 2 * x₁ = u ^ 2 * x₂ ∧
        u ^ 3 * y₁ = (shortCurve B).toAffine.negY (u ^ 2 * x₂) (u ^ 3 * y₂)) := by
      rw [shortCurve_negY] at hxy ⊢
      rintro ⟨h1, h2⟩
      exact hxy ⟨mul_left_cancel₀ hu2 h1, mul_left_cancel₀ hu3 (by linear_combination h2)⟩
    rw [Point.add_some hxy, scalePoint_some, scalePoint_some, scalePoint_some, Point.add_some hxy']
    simp only [Point.some.injEq, Affine.addX, Affine.addY, Affine.negAddY, shortCurve_negY,
      shortCurve_slope_scale hu A B x₁ x₂ y₁ y₂ hB, shortCurve_a₁, shortCurve_a₂]
    constructor <;> ring

/-- The scaling isomorphism `E_A(F) ≃+ E_B(F)`, `(x, y) ↦ (u² x, u³ y)`, for `B = u⁴ A`. -/
def scaleEquiv (hu : u ≠ 0) (hB : B = u ^ 4 * A) :
    (shortCurve A).toAffine.Point ≃+ (shortCurve B).toAffine.Point where
  toFun := scalePoint hu hB
  invFun := scalePoint (inv_ne_zero hu) (by rw [hB, inv_pow, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 4 hu), one_mul])
  left_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · simp only [scalePoint_some, Point.some.injEq]
      constructor <;> field_simp
  right_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · simp only [scalePoint_some, Point.some.injEq]
      constructor <;> field_simp
  map_add' := scalePoint_add hu hB

@[simp] theorem scaleEquiv_zero (hu : u ≠ 0) (hB : B = u ^ 4 * A) :
    scaleEquiv hu hB 0 = 0 := rfl

theorem scaleEquiv_some (hu : u ≠ 0) (hB : B = u ^ 4 * A) {x y : F}
    (h : (shortCurve A).toAffine.Nonsingular x y) :
    scaleEquiv hu hB (.some x y h) = .some _ _ (shortCurve_nonsingular_scale hu hB h) := rfl

theorem scaleEquiv_some_eq (hu : u ≠ 0) (hB : B = u ^ 4 * A) {x y x' y' : F}
    (h : (shortCurve A).toAffine.Nonsingular x y) (h' : (shortCurve B).toAffine.Nonsingular x' y')
    (hx : x' = u ^ 2 * x) (hy : y' = u ^ 3 * y) :
    scaleEquiv hu hB (.some x y h) = .some x' y' h' := by
  subst hx hy; rfl

theorem scaleEquiv_symm_some (hu : u ≠ 0) (hB : B = u ^ 4 * A) {x y : F}
    (h : (shortCurve B).toAffine.Nonsingular x y) :
    ∃ h' : (shortCurve A).toAffine.Nonsingular (u⁻¹ ^ 2 * x) (u⁻¹ ^ 3 * y),
      (scaleEquiv hu hB).symm (.some x y h) = .some _ _ h' := ⟨_, rfl⟩

end Scale

end ZInQ
