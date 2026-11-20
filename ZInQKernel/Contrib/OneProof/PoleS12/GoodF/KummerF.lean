import ZInQKernel.Contrib.PoleRC.KummerM

/-!
# The Kummer maps of `y² = x(x − ℓ)(x + 3ℓ)` over a field of characteristic not `2`, `3`

A copy of round 1's `ZInQKernel/Contrib/PoleRC/KummerM.lean` (written over `ℚ`) for a general
field `F` with `2, 3 ≠ 0`, for use over `𝔽_p` (the proof of `LocalGoodUnram`). Silverman X.1.4.
-/

namespace ZInQ.Manuscript.PoleS12.GoodF

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent Polynomial

open scoped Classical

/-- `y² = x(x − ℓ)(x + 3ℓ) = x³ + 2ℓx² − 3ℓ²x` over `F`. -/
def curveF {F : Type*} [Field F] (ℓ : F) : WeierstrassCurve F := ⟨0, 2 * ℓ, 0, -3 * ℓ ^ 2, 0⟩

variable {F : Type*} [Field F] {ℓ : F}

theorem curve_equation_iff (x y : F) :
    (curveF ℓ).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + 2 * ℓ * x ^ 2 - 3 * ℓ ^ 2 * x := by
  rw [Affine.equation_iff]
  simp only [curveF]
  constructor <;> intro h <;> linear_combination h

@[simp] theorem curveF_a₁ : (curveF ℓ).a₁ = 0 := rfl
@[simp] theorem curveF_a₂ : (curveF ℓ).a₂ = 2 * ℓ := rfl
@[simp] theorem curveF_a₃ : (curveF ℓ).a₃ = 0 := rfl
@[simp] theorem curveF_a₄ : (curveF ℓ).a₄ = -3 * ℓ ^ 2 := rfl
@[simp] theorem curveF_a₆ : (curveF ℓ).a₆ = 0 := rfl

theorem curve_negY (x y : F) : (curveF ℓ).toAffine.negY x y = -y := by
  simp [Affine.negY, curveF]

theorem curveF_Δ (ℓ : F) : (curveF ℓ).Δ = 2304 * ℓ ^ 6 := by
  simp only [curveF, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]; ring

theorem curve_Δ_ne_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) :
    (curveF ℓ).Δ ≠ 0 := by
  rw [curveF_Δ, show (2304 : F) = 2 ^ 8 * 3 ^ 2 by norm_num]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)) (pow_ne_zero 6 hℓ)

theorem curve_nonsingular (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) {x y : F}
    (h : (curveF ℓ).toAffine.Equation x y) : (curveF ℓ).toAffine.Nonsingular x y :=
  (equation_iff_nonsingular_of_Δ_ne_zero (curve_Δ_ne_zero h2 h3 hℓ)).mp h

/-- `e` is a root of `x³ + 2ℓx² − 3ℓ²x`. -/
def IsRootM (ℓ e : F) : Prop := e ^ 3 + 2 * ℓ * e ^ 2 - 3 * ℓ ^ 2 * e = 0

/-- `f'(e) = 3e² + 4ℓe − 3ℓ²`. -/
def fd (ℓ e : F) : F := 3 * e ^ 2 + 4 * ℓ * e - 3 * ℓ ^ 2

theorem fd_ne_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) {e : F}
    (he : IsRootM ℓ e) : fd ℓ e ≠ 0 := by
  have h : e * (e - ℓ) * (e + 3 * ℓ) = 0 := by unfold IsRootM at he; linear_combination he
  unfold fd
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · subst h
      rw [show 3 * (0 : F) ^ 2 + 4 * ℓ * 0 - 3 * ℓ ^ 2 = -(3 * ℓ ^ 2) by ring, neg_ne_zero]
      exact mul_ne_zero h3 (pow_ne_zero 2 hℓ)
    · have : e = ℓ := by linear_combination h
      subst this
      rw [show 3 * e ^ 2 + 4 * e * e - 3 * e ^ 2 = 2 ^ 2 * e ^ 2 by ring]
      exact mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 2 hℓ)
  · have : e = -3 * ℓ := by linear_combination h
    subst this
    rw [show 3 * (-3 * ℓ) ^ 2 + 4 * ℓ * (-3 * ℓ) - 3 * ℓ ^ 2 = 2 ^ 2 * 3 * ℓ ^ 2 by ring]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h2) h3) (pow_ne_zero 2 hℓ)

/-- **The Kummer map of `E_ℓ` at the root `e`.** -/
noncomputable def kum (ℓ e : F) : (curveF ℓ).toAffine.Point → SqClass F
  | 0 => 1
  | .some x _ _ => if x = e then sqc (fd ℓ e) else sqc (x - e)

@[simp] theorem kum_zero (e : F) : kum ℓ e 0 = 1 := rfl

theorem kum_some {e x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y) :
    kum ℓ e (.some x y h) = if x = e then sqc (fd ℓ e) else sqc (x - e) := rfl

theorem kum_some_of_ne {e x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y) (hx : x ≠ e) :
    kum ℓ e (.some x y h) = sqc (x - e) := by
  simp [kum_some, hx]

theorem kum_some_eq {e x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y) (hx : x = e) :
    kum ℓ e (.some x y h) = sqc (fd ℓ e) := by
  simp [kum_some, hx]

theorem kum_neg (e : F) (P : (curveF ℓ).toAffine.Point) : kum ℓ e (-P) = kum ℓ e P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

theorem y_eq_zero_of_root {e x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y)
    (he : IsRootM ℓ e) (hx : x = e) : y = 0 := by
  have := (curve_equation_iff x y).mp h.1
  rw [hx] at this
  unfold IsRootM at he
  exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (by rw [this, he])

theorem root_equation {e : F} (he : IsRootM ℓ e) : (curveF ℓ).toAffine.Equation e 0 := by
  rw [curve_equation_iff]; unfold IsRootM at he; linear_combination -he

variable (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0) {e : F} (he : IsRootM ℓ e)
include h2 h3 hℓ he

/-- The two-torsion point `(e, 0)`. -/
noncomputable def tPt : (curveF ℓ).toAffine.Point :=
  .some e 0 (curve_nonsingular h2 h3 hℓ (root_equation he))

theorem some_eq_tPt {x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y) (hx : x = e) :
    Point.some x y h = tPt h2 h3 hℓ he := by
  have hy := y_eq_zero_of_root h he hx
  subst hx hy; rfl

theorem kum_tPt : kum ℓ e (tPt h2 h3 hℓ he) = sqc (fd ℓ e) := kum_some_eq _ rfl

/-- `(x, y) + (e, 0)` has abscissa `e + f'(e)/(x − e)` for `x ≠ e`. -/
theorem add_tPt_x {x y : F} (h : (curveF ℓ).toAffine.Nonsingular x y) (hx : x ≠ e) :
    ∃ y' h', Point.some x y h + tPt h2 h3 hℓ he = .some (e + fd ℓ e / (x - e)) y' h' := by
  unfold tPt
  rw [Point.add_of_X_ne hx]
  have hxe : x - e ≠ 0 := sub_ne_zero.mpr hx
  have ex : (curveF ℓ).toAffine.addX x e ((curveF ℓ).toAffine.slope x e y 0) =
      e + fd ℓ e / (x - e) := by
    have hq := (curve_equation_iff x y).mp h.1
    rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addX, curveF, fd, sub_zero, zero_mul, add_zero]
    unfold IsRootM at he
    field_simp
    linear_combination hq + he
  have hn := nonsingular_add h (curve_nonsingular h2 h3 hℓ (root_equation he)) (fun hxy => hx hxy.left)
  rw [ex] at hn
  exact ⟨_, hn, by simp only [Point.some.injEq]; exact ⟨ex, trivial⟩⟩

theorem kum_add_tPt (P : (curveF ℓ).toAffine.Point) :
    kum ℓ e (P + tPt h2 h3 hℓ he) = kum ℓ e P * sqc (fd ℓ e) := by
  have hc := fd_ne_zero h2 h3 hℓ he
  rcases P with _ | ⟨x, y, h⟩
  · rw [show (Point.zero : (curveF ℓ).toAffine.Point) = 0 from rfl, zero_add, kum_tPt, kum_zero,
      one_mul]
  · by_cases hx : x = e
    · rw [some_eq_tPt h2 h3 hℓ he h hx]
      unfold tPt
      rw [Point.add_self_of_Y_eq (by simp [curve_negY]), kum_some_eq _ rfl]
      simp [SqClass.mul_self]
    · obtain ⟨y', h', eq⟩ := add_tPt_x h2 h3 hℓ he h hx
      have hxe : x - e ≠ 0 := sub_ne_zero.mpr hx
      have hne : e + fd ℓ e / (x - e) ≠ e := by
        intro h0
        have : fd ℓ e / (x - e) = 0 := by linear_combination h0
        exact div_ne_zero hc hxe this
      rw [eq, kum_some_of_ne _ hne, kum_some_of_ne _ hx, add_sub_cancel_left,
        sqc_div hc hxe, mul_comm]

omit h2 h3 hℓ in
/-- **The chord-tangent identity at the root `e`.** -/
theorem mul_addX_sub_eq_M {x₁ x₂ y₁ y₂ : F} (h₁ : (curveF ℓ).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveF ℓ).toAffine.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (curveF ℓ).toAffine.negY x₂ y₂)) :
    (x₁ - e) * (x₂ - e) *
        ((curveF ℓ).toAffine.addX x₁ x₂ ((curveF ℓ).toAffine.slope x₁ x₂ y₁ y₂) - e) =
      (y₁ - (curveF ℓ).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - e)) ^ 2 := by
  have key := congrArg (Polynomial.eval e) (Affine.addPolynomial_slope h₁.1 h₂.1 hxy)
  rw [Affine.addPolynomial_eq] at key
  simp only [Cubic.toPoly, eval_neg, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_sub,
    curveF_a₁, curveF_a₂, curveF_a₃, curveF_a₄, curveF_a₆] at key
  unfold IsRootM at he
  linear_combination -key - he

theorem kum_add (P Q : (curveF ℓ).toAffine.Point) :
    kum ℓ e (P + Q) = kum ℓ e P * kum ℓ e Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · show kum ℓ e (0 + _) = kum ℓ e 0 * _
    rw [zero_add, kum_zero, one_mul]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · show kum ℓ e (_ + 0) = _ * kum ℓ e 0
    rw [add_zero, kum_zero, mul_one]
  by_cases hx₁ : x₁ = e
  · rw [some_eq_tPt h2 h3 hℓ he h₁ hx₁, add_comm, kum_add_tPt, kum_tPt, mul_comm]
  by_cases hx₂ : x₂ = e
  · rw [some_eq_tPt h2 h3 hℓ he h₂ hx₂, kum_add_tPt, kum_tPt]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (curveF ℓ).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2, kum_zero, kum_some_of_ne _ hx₁,
      kum_some_of_ne _ hx₂, hxy.1, SqClass.mul_self]
  have key := mul_addX_sub_eq_M he h₁ h₂ hxy
  rw [Point.add_some hxy]
  by_cases hx₃ : (curveF ℓ).toAffine.addX x₁ x₂ ((curveF ℓ).toAffine.slope x₁ x₂ y₁ y₂) = e
  · have hPQ : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = tPt h2 h3 hℓ he := by
      rw [Point.add_some hxy]; exact some_eq_tPt h2 h3 hℓ he _ hx₃
    have hQ : Point.some x₂ y₂ h₂ = -Point.some x₁ y₁ h₁ + tPt h2 h3 hℓ he := by
      rw [← hPQ]; abel
    rw [some_eq_tPt h2 h3 hℓ he _ hx₃, hQ, kum_add_tPt, kum_neg, kum_tPt,
      ← mul_assoc, SqClass.mul_self, one_mul]
  · rw [kum_some_of_ne _ hx₁, kum_some_of_ne _ hx₂, kum_some_of_ne _ hx₃]
    have h1 : x₁ - e ≠ 0 := sub_ne_zero.mpr hx₁
    have h2' : x₂ - e ≠ 0 := sub_ne_zero.mpr hx₂
    have h3 : (curveF ℓ).toAffine.addX x₁ x₂ ((curveF ℓ).toAffine.slope x₁ x₂ y₁ y₂) - e ≠ 0 :=
      sub_ne_zero.mpr hx₃
    have hν : y₁ - (curveF ℓ).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - e) ≠ 0 := by
      intro h0
      rw [h0] at key
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_eq_zero] at key
      tauto
    have : (curveF ℓ).toAffine.addX x₁ x₂ ((curveF ℓ).toAffine.slope x₁ x₂ y₁ y₂) - e =
        (x₁ - e) * (x₂ - e) * ((y₁ - (curveF ℓ).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - e)) /
          ((x₁ - e) * (x₂ - e))) ^ 2 := by
      have hx12 : (x₁ - e) * (x₂ - e) ≠ 0 := mul_ne_zero h1 h2'
      rw [div_pow, ← key]
      field_simp
    rw [this, sqc_mul_sq _ (div_ne_zero hν (mul_ne_zero h1 h2')), sqc_mul h1 h2']

end ZInQ.Manuscript.PoleS12.GoodF
