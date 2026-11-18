import ZInQKernel.Contrib.PoleRC.CRM
import ZInQKernel.RouteK.Rank.Image

/-!
# The Kummer maps of `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` at its roots

For a root `e ∈ {0, ℓ, −3ℓ}` of `f(x) = x³ + 2ℓx² − 3ℓ²x`, `kum ℓ e : E_ℓ(ℚ) → ℚ*/ℚ*²` is
`O ↦ 1`, `(e, 0) ↦ f'(e) = 3e² + 4ℓe − 3ℓ²`, `(x, y) ↦ x − e` otherwise. `kum_add`: it is a
homomorphism (Silverman X.1.4). The proof follows Route K's `RouteK.Rank.kummerAt_add` (for
`y² = x³ + bx`); the chord identity `(x₁ − e)(x₂ − e)(x₃ − e) = (y₁ − λ(x₁ − e))²` is read off
Mathlib's `addPolynomial_slope` at `X = e`.
-/

namespace ZInQ.Manuscript.PoleRC

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent Polynomial

variable {ℓ : ℚ}

theorem curve_equation_iff (x y : ℚ) :
    (curve ℓ).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + 2 * ℓ * x ^ 2 - 3 * ℓ ^ 2 * x := by
  rw [Affine.equation_iff]
  simp only [curve]
  constructor <;> intro h <;> linear_combination h

@[simp] theorem curve_a₁ : (curve ℓ).a₁ = 0 := rfl
@[simp] theorem curve_a₂ : (curve ℓ).a₂ = 2 * ℓ := rfl
@[simp] theorem curve_a₃ : (curve ℓ).a₃ = 0 := rfl
@[simp] theorem curve_a₄ : (curve ℓ).a₄ = -3 * ℓ ^ 2 := rfl
@[simp] theorem curve_a₆ : (curve ℓ).a₆ = 0 := rfl

theorem curve_negY (x y : ℚ) : (curve ℓ).toAffine.negY x y = -y := by
  simp [Affine.negY, curve]

theorem curve_Δ_ne_zero (hℓ : ℓ ≠ 0) : (curve ℓ).Δ ≠ 0 := by
  rw [curve_Δ]; exact mul_ne_zero (by norm_num) (pow_ne_zero 6 hℓ)

theorem curve_nonsingular (hℓ : ℓ ≠ 0) {x y : ℚ} (h : (curve ℓ).toAffine.Equation x y) :
    (curve ℓ).toAffine.Nonsingular x y :=
  (equation_iff_nonsingular_of_Δ_ne_zero (curve_Δ_ne_zero hℓ)).mp h

/-- `e` is a root of `x³ + 2ℓx² − 3ℓ²x`. -/
def IsRootM (ℓ e : ℚ) : Prop := e ^ 3 + 2 * ℓ * e ^ 2 - 3 * ℓ ^ 2 * e = 0

/-- `f'(e) = 3e² + 4ℓe − 3ℓ²`. -/
def fd (ℓ e : ℚ) : ℚ := 3 * e ^ 2 + 4 * ℓ * e - 3 * ℓ ^ 2

theorem fd_ne_zero (hℓ : ℓ ≠ 0) {e : ℚ} (he : IsRootM ℓ e) : fd ℓ e ≠ 0 := by
  have h : e * (e - ℓ) * (e + 3 * ℓ) = 0 := by unfold IsRootM at he; linear_combination he
  unfold fd
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · subst h; intro h0; apply hℓ; nlinarith [sq_nonneg ℓ]
    · have : e = ℓ := by linear_combination h
      subst this; intro h0; apply hℓ; nlinarith [sq_nonneg e]
  · have : e = -3 * ℓ := by linear_combination h
    subst this; intro h0; apply hℓ; nlinarith [sq_nonneg ℓ]

/-- **The Kummer map of `E_ℓ` at the root `e`.** -/
noncomputable def kum (ℓ e : ℚ) : (curve ℓ).toAffine.Point → SqClass ℚ
  | 0 => 1
  | .some x _ _ => if x = e then sqc (fd ℓ e) else sqc (x - e)

@[simp] theorem kum_zero (e : ℚ) : kum ℓ e 0 = 1 := rfl

theorem kum_some {e x y : ℚ} (h : (curve ℓ).toAffine.Nonsingular x y) :
    kum ℓ e (.some x y h) = if x = e then sqc (fd ℓ e) else sqc (x - e) := rfl

theorem kum_some_of_ne {e x y : ℚ} (h : (curve ℓ).toAffine.Nonsingular x y) (hx : x ≠ e) :
    kum ℓ e (.some x y h) = sqc (x - e) := by
  simp [kum_some, hx]

theorem kum_some_eq {e x y : ℚ} (h : (curve ℓ).toAffine.Nonsingular x y) (hx : x = e) :
    kum ℓ e (.some x y h) = sqc (fd ℓ e) := by
  simp [kum_some, hx]

theorem kum_neg (e : ℚ) (P : (curve ℓ).toAffine.Point) : kum ℓ e (-P) = kum ℓ e P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

theorem y_eq_zero_of_root {e x y : ℚ} (h : (curve ℓ).toAffine.Nonsingular x y)
    (he : IsRootM ℓ e) (hx : x = e) : y = 0 := by
  have := (curve_equation_iff x y).mp h.1
  rw [hx] at this
  unfold IsRootM at he
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [this, he])

theorem root_equation {e : ℚ} (he : IsRootM ℓ e) : (curve ℓ).toAffine.Equation e 0 := by
  rw [curve_equation_iff]; unfold IsRootM at he; linear_combination -he

variable (hℓ : ℓ ≠ 0) {e : ℚ} (he : IsRootM ℓ e)
include hℓ he

/-- The two-torsion point `(e, 0)`. -/
noncomputable def tPt : (curve ℓ).toAffine.Point :=
  .some e 0 (curve_nonsingular hℓ (root_equation he))

theorem some_eq_tPt {x y : ℚ} (h : (curve ℓ).toAffine.Nonsingular x y) (hx : x = e) :
    Point.some x y h = tPt hℓ he := by
  have hy := y_eq_zero_of_root h he hx
  subst hx hy; rfl

theorem kum_tPt : kum ℓ e (tPt hℓ he) = sqc (fd ℓ e) := kum_some_eq _ rfl

/-- `(x, y) + (e, 0)` has abscissa `e + f'(e)/(x − e)` for `x ≠ e`. -/
theorem add_tPt_x {x y : ℚ} (h : (curve ℓ).toAffine.Nonsingular x y) (hx : x ≠ e) :
    ∃ y' h', Point.some x y h + tPt hℓ he = .some (e + fd ℓ e / (x - e)) y' h' := by
  unfold tPt
  rw [Point.add_of_X_ne hx]
  have hxe : x - e ≠ 0 := sub_ne_zero.mpr hx
  have ex : (curve ℓ).toAffine.addX x e ((curve ℓ).toAffine.slope x e y 0) =
      e + fd ℓ e / (x - e) := by
    have hq := (curve_equation_iff x y).mp h.1
    rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addX, curve, fd, sub_zero, zero_mul, add_zero]
    unfold IsRootM at he
    field_simp
    linear_combination hq + he
  have hn := nonsingular_add h (curve_nonsingular hℓ (root_equation he)) (fun hxy => hx hxy.left)
  rw [ex] at hn
  exact ⟨_, hn, by simp only [Point.some.injEq]; exact ⟨ex, trivial⟩⟩

theorem kum_add_tPt (P : (curve ℓ).toAffine.Point) :
    kum ℓ e (P + tPt hℓ he) = kum ℓ e P * sqc (fd ℓ e) := by
  have hc := fd_ne_zero hℓ he
  rcases P with _ | ⟨x, y, h⟩
  · rw [show (Point.zero : (curve ℓ).toAffine.Point) = 0 from rfl, zero_add, kum_tPt, kum_zero,
      one_mul]
  · by_cases hx : x = e
    · rw [some_eq_tPt hℓ he h hx]
      unfold tPt
      rw [Point.add_self_of_Y_eq (by simp [curve_negY]), kum_some_eq _ rfl]
      simp [SqClass.mul_self]
    · obtain ⟨y', h', eq⟩ := add_tPt_x hℓ he h hx
      have hxe : x - e ≠ 0 := sub_ne_zero.mpr hx
      have hne : e + fd ℓ e / (x - e) ≠ e := by
        intro h0
        have : fd ℓ e / (x - e) = 0 := by linear_combination h0
        exact div_ne_zero hc hxe this
      rw [eq, kum_some_of_ne _ hne, kum_some_of_ne _ hx, add_sub_cancel_left,
        sqc_div hc hxe, mul_comm]

omit hℓ in
/-- **The chord-tangent identity at the root `e`.** -/
theorem mul_addX_sub_eq_M {x₁ x₂ y₁ y₂ : ℚ} (h₁ : (curve ℓ).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve ℓ).toAffine.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (curve ℓ).toAffine.negY x₂ y₂)) :
    (x₁ - e) * (x₂ - e) *
        ((curve ℓ).toAffine.addX x₁ x₂ ((curve ℓ).toAffine.slope x₁ x₂ y₁ y₂) - e) =
      (y₁ - (curve ℓ).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - e)) ^ 2 := by
  have key := congrArg (Polynomial.eval e) (Affine.addPolynomial_slope h₁.1 h₂.1 hxy)
  rw [Affine.addPolynomial_eq] at key
  simp only [Cubic.toPoly, eval_neg, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_sub,
    curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆] at key
  unfold IsRootM at he
  linear_combination -key - he

theorem kum_add (P Q : (curve ℓ).toAffine.Point) :
    kum ℓ e (P + Q) = kum ℓ e P * kum ℓ e Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · show kum ℓ e (0 + _) = kum ℓ e 0 * _
    rw [zero_add, kum_zero, one_mul]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · show kum ℓ e (_ + 0) = _ * kum ℓ e 0
    rw [add_zero, kum_zero, mul_one]
  by_cases hx₁ : x₁ = e
  · rw [some_eq_tPt hℓ he h₁ hx₁, add_comm, kum_add_tPt, kum_tPt, mul_comm]
  by_cases hx₂ : x₂ = e
  · rw [some_eq_tPt hℓ he h₂ hx₂, kum_add_tPt, kum_tPt]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (curve ℓ).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2, kum_zero, kum_some_of_ne _ hx₁,
      kum_some_of_ne _ hx₂, hxy.1, SqClass.mul_self]
  have key := mul_addX_sub_eq_M he h₁ h₂ hxy
  rw [Point.add_some hxy]
  by_cases hx₃ : (curve ℓ).toAffine.addX x₁ x₂ ((curve ℓ).toAffine.slope x₁ x₂ y₁ y₂) = e
  · have hPQ : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = tPt hℓ he := by
      rw [Point.add_some hxy]; exact some_eq_tPt hℓ he _ hx₃
    have hQ : Point.some x₂ y₂ h₂ = -Point.some x₁ y₁ h₁ + tPt hℓ he := by
      rw [← hPQ]; abel
    rw [some_eq_tPt hℓ he _ hx₃, hQ, kum_add_tPt, kum_neg, kum_tPt,
      ← mul_assoc, SqClass.mul_self, one_mul]
  · rw [kum_some_of_ne _ hx₁, kum_some_of_ne _ hx₂, kum_some_of_ne _ hx₃]
    have h1 : x₁ - e ≠ 0 := sub_ne_zero.mpr hx₁
    have h2' : x₂ - e ≠ 0 := sub_ne_zero.mpr hx₂
    have h3 : (curve ℓ).toAffine.addX x₁ x₂ ((curve ℓ).toAffine.slope x₁ x₂ y₁ y₂) - e ≠ 0 :=
      sub_ne_zero.mpr hx₃
    have hν : y₁ - (curve ℓ).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - e) ≠ 0 := by
      intro h0
      rw [h0] at key
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_eq_zero] at key
      tauto
    have : (curve ℓ).toAffine.addX x₁ x₂ ((curve ℓ).toAffine.slope x₁ x₂ y₁ y₂) - e =
        (x₁ - e) * (x₂ - e) * ((y₁ - (curve ℓ).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - e)) /
          ((x₁ - e) * (x₂ - e))) ^ 2 := by
      have hx12 : (x₁ - e) * (x₂ - e) ≠ 0 := mul_ne_zero h1 h2'
      rw [div_pow, ← key]
      field_simp
    rw [this, sqc_mul_sq _ (div_ne_zero hν (mul_ne_zero h1 h2')), sqc_mul h1 h2']

end ZInQ.Manuscript.PoleRC
