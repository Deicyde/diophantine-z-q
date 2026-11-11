import ZInQKernel.Model.Descent.Kummer

/-!
# The Kummer map at a root of the cubic

For a field `K`, `b ∈ K` and a root `e` of `x³ + b x` (`e³ + b e = 0`), the map
`kummerAt b e : E_b(K) → K*/K*²` on `E_b : y² = x³ + b x` (`shortCurve b`) is

* `O ↦ 1`, `(e, 0) ↦ 3e² + b` (that is `(e − e')(e − e'')` for the other two roots),
* `(x, y) ↦ x − e` for `x ≠ e`.

For `e = 0` this is `Descent.kummer b`. The main result is `kummerAt_add`: it is a homomorphism
(Silverman X.1.4, one coordinate of the complete 2-descent). The proof follows
`Descent.kummer_add`; the chord identity is `mul_addX_sub_eq`:
`(x₁ − e)(x₂ − e)(x₃ − e) = (y₁ − ℓ (x₁ − e))²`.
-/

namespace ZInQ.RouteK.Rank

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent

variable {K : Type*} [Field K] [DecidableEq K]

/-- The Kummer map attached to the root `e` of `x³ + b x`: `O ↦ 1`, `(e, 0) ↦ 3e² + b`,
`(x, y) ↦ x − e` otherwise, in `K*/K*²`. -/
noncomputable def kummerAt (b e : K) : (shortCurve b).toAffine.Point → SqClass K
  | 0 => 1
  | .some x _ _ => if x = e then sqc (3 * e ^ 2 + b) else sqc (x - e)

variable {b e : K}

@[simp] theorem kummerAt_zero : kummerAt b e 0 = 1 := rfl

theorem kummerAt_some {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y) :
    kummerAt b e (.some x y h) = if x = e then sqc (3 * e ^ 2 + b) else sqc (x - e) := rfl

theorem kummerAt_some_of_ne {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y)
    (hx : x ≠ e) : kummerAt b e (.some x y h) = sqc (x - e) := by
  simp [kummerAt_some, hx]

theorem kummerAt_some_eq {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y) (hx : x = e) :
    kummerAt b e (.some x y h) = sqc (3 * e ^ 2 + b) := by
  simp [kummerAt_some, hx]

theorem kummerAt_neg (P : (shortCurve b).toAffine.Point) : kummerAt b e (-P) = kummerAt b e P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

omit [DecidableEq K] in
/-- The root `e` is simple: `3e² + b ≠ 0`. -/
theorem kummerAt_root_ne_zero (h2 : (2 : K) ≠ 0) (hb : b ≠ 0) (he : e ^ 3 + b * e = 0) :
    3 * e ^ 2 + b ≠ 0 := by
  intro h
  have h' : e * (e ^ 2 + b) = 0 := by linear_combination he
  rcases mul_eq_zero.mp h' with h0 | h0
  · subst h0; apply hb; linear_combination h
  · apply hb
    have : (2 : K) * b = 0 := by linear_combination 3 * h0 - h
    exact (mul_eq_zero.mp this).resolve_left h2

omit [DecidableEq K] in
/-- On `E_b`, a point with abscissa the root `e` has ordinate `0`. -/
theorem kummerAt_y_eq_zero {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y)
    (he : e ^ 3 + b * e = 0) (hx : x = e) : y = 0 := by
  have := (shortCurve_equation_iff b x y).mp h.1
  rw [hx, he] at this
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

omit [DecidableEq K] in
theorem kummerAt_tRoot_equation (he : e ^ 3 + b * e = 0) :
    (shortCurve b).toAffine.Equation e 0 := by
  rw [shortCurve_equation_iff]; linear_combination -he

variable (h2 : (2 : K) ≠ 0) (hb : b ≠ 0) (he : e ^ 3 + b * e = 0)
include h2 hb

/-- The two-torsion point `(e, 0)`. -/
noncomputable def tRootPt : (shortCurve b).toAffine.Point :=
  have : NeZero (2 : K) := ⟨h2⟩
  have : (shortCurve b).IsElliptic := shortCurve_isElliptic hb
  Point.mk (kummerAt_tRoot_equation he)

omit [DecidableEq K] in
include he in
theorem tRootPt_def : ∃ h, tRootPt h2 hb he = .some e 0 h := ⟨_, rfl⟩

omit [DecidableEq K] in
include he in
theorem some_eq_tRootPt {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y) (hx : x = e) :
    Point.some x y h = tRootPt h2 hb he := by
  have hy := kummerAt_y_eq_zero h he hx
  subst hx hy; rfl

include he in
theorem kummerAt_tRootPt : kummerAt b e (tRootPt h2 hb he) = sqc (3 * e ^ 2 + b) := by
  obtain ⟨h, e'⟩ := tRootPt_def h2 hb he
  rw [e', kummerAt_some_eq _ rfl]

include he in
/-- `(x, y) + (e, 0)` has abscissa `e + (3e² + b)/(x − e)` for `x ≠ e`. -/
theorem add_tRootPt_x {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y) (hx : x ≠ e) :
    ∃ y' h', Point.some x y h + tRootPt h2 hb he =
      .some (e + (3 * e ^ 2 + b) / (x - e)) y' h' := by
  obtain ⟨h0, ht⟩ := tRootPt_def h2 hb he
  rw [ht, Point.add_of_X_ne hx]
  have hxe : x - e ≠ 0 := sub_ne_zero.mpr hx
  have ex : (shortCurve b).toAffine.addX x e ((shortCurve b).toAffine.slope x e y 0) =
      e + (3 * e ^ 2 + b) / (x - e) := by
    have hq := (shortCurve_equation_iff b x y).mp h.1
    rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addX, shortCurve_a₁, shortCurve_a₂, sub_zero, zero_mul, add_zero]
    field_simp
    linear_combination hq + he
  have hn := nonsingular_add h h0 (fun hxy => hx hxy.left)
  rw [ex] at hn
  exact ⟨_, hn, by simp only [Point.some.injEq]; exact ⟨ex, trivial⟩⟩

include he in
theorem kummerAt_add_tRootPt (P : (shortCurve b).toAffine.Point) :
    kummerAt b e (P + tRootPt h2 hb he) = kummerAt b e P * sqc (3 * e ^ 2 + b) := by
  have hc := kummerAt_root_ne_zero h2 hb he
  rcases P with _ | ⟨x, y, h⟩
  · rw [show (Point.zero : (shortCurve b).toAffine.Point) = 0 from rfl, zero_add,
      kummerAt_tRootPt, kummerAt_zero, one_mul]
  · by_cases hx : x = e
    · rw [some_eq_tRootPt h2 hb he h hx]
      obtain ⟨h0, ht⟩ := tRootPt_def h2 hb he
      rw [ht, Point.add_self_of_Y_eq (by simp), kummerAt_some_eq _ rfl]
      simp [SqClass.mul_self]
    · obtain ⟨y', h', eq⟩ := add_tRootPt_x h2 hb he h hx
      have hxe : x - e ≠ 0 := sub_ne_zero.mpr hx
      have hne : e + (3 * e ^ 2 + b) / (x - e) ≠ e := by
        intro h0
        have : (3 * e ^ 2 + b) / (x - e) = 0 := by linear_combination h0
        exact div_ne_zero hc hxe this
      rw [eq, kummerAt_some_of_ne _ hne, kummerAt_some_of_ne _ hx, add_sub_cancel_left,
        sqc_div hc hxe, mul_comm]

omit hb in
include he in
/-- The chord-tangent identity at the root `e`: if `(x₁, y₁) + (x₂, y₂)` is affine with slope
`ℓ`, then `(x₁ − e)(x₂ − e)(x₃ − e) = (y₁ − ℓ (x₁ − e))²`. -/
theorem mul_addX_sub_eq {x₁ x₂ y₁ y₂ : K} (h₁ : (shortCurve b).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve b).toAffine.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve b).toAffine.negY x₂ y₂)) :
    (x₁ - e) * (x₂ - e) *
        ((shortCurve b).toAffine.addX x₁ x₂ ((shortCurve b).toAffine.slope x₁ x₂ y₁ y₂) - e) =
      (y₁ - (shortCurve b).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - e)) ^ 2 := by
  have e₁ := (shortCurve_equation_iff b x₁ y₁).mp h₁.1
  have e₂ := (shortCurve_equation_iff b x₂ y₂).mp h₂.1
  simp only [Affine.addX, shortCurve_a₁, shortCurve_a₂, zero_mul, add_zero, sub_zero]
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ -y₂ := by rw [shortCurve_negY] at hxy; exact fun h => hxy ⟨rfl, h⟩
    have hyy : y₁ = y₂ := by
      have : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination e₁ - e₂
      rcases mul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · exact absurd (eq_neg_of_add_eq_zero_left h) hy
    subst hyy
    have hy0 : y₁ - -y₁ ≠ 0 := by
      intro h0; apply hy
      have : (2 : K) * y₁ = 0 := by linear_combination h0
      rw [(mul_eq_zero.mp this).resolve_left h2, neg_zero]
    set ℓ := (shortCurve b).toAffine.slope x₁ x₁ y₁ y₁ with hℓdef
    have hℓ : ℓ * (y₁ - -y₁) = 3 * x₁ ^ 2 + b := by
      rw [hℓdef, Affine.slope_of_Y_ne rfl (by rwa [shortCurve_negY])]
      simp only [shortCurve_negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₄, mul_zero, add_zero,
        sub_zero, zero_mul]
      exact div_mul_cancel₀ _ hy0
    apply mul_right_cancel₀ (pow_ne_zero 2 hy0)
    linear_combination (2 * y₁ * (x₁ - e) * (y₁ - -y₁)) * hℓ + (-4 * y₁ ^ 2) * e₁ +
      (-(y₁ - -y₁) ^ 2) * he
  · set ℓ := (shortCurve b).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hℓ : ℓ * (x₁ - x₂) = y₁ - y₂ := by
      rw [hℓdef, Affine.slope_of_X_ne hx]; field_simp
    apply mul_right_cancel₀ (pow_ne_zero 2 hd)
    linear_combination ((x₁ - x₂) * (e - x₁) * (ℓ * (x₁ - x₂) + (y₁ - y₂)) +
        2 * y₁ * (x₁ - e) * (x₁ - x₂)) * hℓ +
      ((x₂ - e) * (x₁ - x₂)) * e₁ - ((x₁ - e) * (x₁ - x₂)) * e₂ - (x₁ - x₂) ^ 2 * he

include he in
/-- **The Kummer map at a root is a homomorphism.** -/
theorem kummerAt_add (P Q : (shortCurve b).toAffine.Point) :
    kummerAt b e (P + Q) = kummerAt b e P * kummerAt b e Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · show kummerAt b e (0 + _) = kummerAt b e 0 * _
    rw [zero_add, kummerAt_zero, one_mul]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · show kummerAt b e (_ + 0) = _ * kummerAt b e 0
    rw [add_zero, kummerAt_zero, mul_one]
  by_cases hx₁ : x₁ = e
  · rw [some_eq_tRootPt h2 hb he h₁ hx₁, add_comm, kummerAt_add_tRootPt, kummerAt_tRootPt,
      mul_comm]
  by_cases hx₂ : x₂ = e
  · rw [some_eq_tRootPt h2 hb he h₂ hx₂, kummerAt_add_tRootPt, kummerAt_tRootPt]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (shortCurve b).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2, kummerAt_zero, kummerAt_some_of_ne _ hx₁,
      kummerAt_some_of_ne _ hx₂, hxy.1, SqClass.mul_self]
  have key := mul_addX_sub_eq h2 he h₁ h₂ hxy
  rw [Point.add_some hxy]
  set ℓ := (shortCurve b).toAffine.slope x₁ x₂ y₁ y₂
  set x₃ := (shortCurve b).toAffine.addX x₁ x₂ ℓ
  by_cases hx₃ : x₃ = e
  · have hPQ : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = tRootPt h2 hb he := by
      rw [Point.add_some hxy]; exact some_eq_tRootPt h2 hb he _ hx₃
    have hQ : Point.some x₂ y₂ h₂ = -Point.some x₁ y₁ h₁ + tRootPt h2 hb he := by
      rw [← hPQ]; abel
    rw [some_eq_tRootPt h2 hb he _ hx₃, hQ, kummerAt_add_tRootPt, kummerAt_neg, kummerAt_tRootPt,
      ← mul_assoc, SqClass.mul_self, one_mul]
  · rw [kummerAt_some_of_ne _ hx₁, kummerAt_some_of_ne _ hx₂, kummerAt_some_of_ne _ hx₃]
    have h1 : x₁ - e ≠ 0 := sub_ne_zero.mpr hx₁
    have h2' : x₂ - e ≠ 0 := sub_ne_zero.mpr hx₂
    have h3 : x₃ - e ≠ 0 := sub_ne_zero.mpr hx₃
    set ν := y₁ - ℓ * (x₁ - e)
    have hν : ν ≠ 0 := by
      intro h0
      rw [h0] at key
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_eq_zero] at key
      tauto
    have : x₃ - e = (x₁ - e) * (x₂ - e) * (ν / ((x₁ - e) * (x₂ - e))) ^ 2 := by
      have hx12 : (x₁ - e) * (x₂ - e) ≠ 0 := mul_ne_zero h1 h2'
      rw [div_pow, ← key]
      field_simp
    rw [this, sqc_mul_sq _ (div_ne_zero hν (mul_ne_zero h1 h2')), sqc_mul h1 h2']

include he in
/-- The Kummer map at a root as a homomorphism `E_b(K) →+ Additive (K*/K*²)`. -/
noncomputable def kummerAtHom : (shortCurve b).toAffine.Point →+ Additive (SqClass K) where
  toFun P := Additive.ofMul (kummerAt b e P)
  map_zero' := rfl
  map_add' P Q := by rw [kummerAt_add h2 hb he]; rfl

end ZInQ.RouteK.Rank
