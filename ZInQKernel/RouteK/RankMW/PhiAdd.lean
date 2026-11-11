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

/-! ### `φ` and the two-torsion point -/

section Phi

variable [DecidableEq K] {b b' : K} [(shortCurve b).IsElliptic] [(shortCurve b').IsElliptic]
  (hb' : b' = -4 * b)

include hb' in
/-- `φ(-P) = -φ(P)`. -/
theorem mwPhi_neg (P : (shortCurve b).toAffine.Point) : phi hb' (-P) = -phi hb' P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  rw [Point.neg_some]
  by_cases hx : x = 0
  · rw [phi_some_of_eq_zero _ _ hx, phi_some_of_eq_zero _ _ hx]; rfl
  rw [phi_some _ _ hx, phi_some _ _ hx]
  simp only [Point.mk, Point.neg_some, Point.some.injEq, shortCurve_negY]
  constructor
  · ring
  · ring

/-- `(x, y) + (0, 0) = (b/x, -b y/x²)`. -/
theorem mwAdd_tZero_some {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y) (hx : x ≠ 0) :
    ∃ h', Point.some x y h + tZero = .some (b / x) (-(b * y) / x ^ 2) h' := by
  obtain ⟨h0, ht⟩ := tZero_def (b := b)
  rw [ht, Point.add_of_X_ne hx]
  have he := (shortCurve_equation_iff b x y).mp h.1
  have ex : (shortCurve b).toAffine.addX x 0 ((shortCurve b).toAffine.slope x 0 y 0) = b / x := by
    rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addX, shortCurve_a₁, shortCurve_a₂, sub_zero, zero_mul, add_zero]
    field_simp
    linear_combination he
  have ey : (shortCurve b).toAffine.addY x 0 y ((shortCurve b).toAffine.slope x 0 y 0) =
      -(b * y) / x ^ 2 := by
    rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, shortCurve_a₁,
      shortCurve_a₂, shortCurve_a₃, sub_zero, zero_mul, add_zero]
    field_simp
    linear_combination (-y) * he
  have hn := nonsingular_add h h0 (fun hxy => hx hxy.left)
  rw [ex, ey] at hn
  exact ⟨hn, by simp only [Point.some.injEq]; exact ⟨ex, ey⟩⟩

theorem mwTZero_add_tZero : (tZero : (shortCurve b).toAffine.Point) + tZero = 0 := by
  obtain ⟨h0, ht⟩ := tZero_def (b := b)
  rw [ht]
  exact Point.add_self_of_Y_eq (by rw [shortCurve_negY, neg_zero])

theorem mwNeg_tZero : -(tZero : (shortCurve b).toAffine.Point) = tZero := by
  rw [neg_eq_iff_add_eq_zero, mwTZero_add_tZero]

include hb' in
theorem mwPhi_tZero : phi hb' (tZero : (shortCurve b).toAffine.Point) = 0 := by
  obtain ⟨h0, ht⟩ := tZero_def (b := b)
  rw [ht, phi_some_of_eq_zero _ _ rfl]

include hb' in
/-- `φ(P + (0,0)) = φ(P)`. -/
theorem mwPhi_add_tZero (P : (shortCurve b).toAffine.Point) : phi hb' (P + tZero) = phi hb' P := by
  have hb : b ≠ 0 := ne_zero_of_isElliptic
  rcases P with _ | ⟨x, y, h⟩
  · show phi hb' (0 + tZero) = phi hb' 0
    rw [zero_add, mwPhi_tZero, phi_zero]
  by_cases hx : x = 0
  · rw [some_eq_tZero h hx, mwTZero_add_tZero, phi_zero, mwPhi_tZero]
  obtain ⟨h', e⟩ := mwAdd_tZero_some h hx
  rw [e, phi_some _ _ (div_ne_zero hb hx), phi_some _ _ hx]
  simp only [Point.mk, Point.some.injEq]
  constructor
  · field_simp
  · field_simp
    ring

include hb' in
/-- Additivity of `φ` in the generic case: `x₁ ≠ x₂`, `x₁ x₂ ≠ b`, all abscissas nonzero. -/
theorem mwPhi_add_generic {x₁ y₁ x₂ y₂ : K} (h₁ : (shortCurve b).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve b).toAffine.Nonsingular x₂ y₂) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hx : x₁ ≠ x₂) (hb : x₁ * x₂ ≠ b)
    (hx₃ : (shortCurve b).toAffine.addX x₁ x₂ ((shortCurve b).toAffine.slope x₁ x₂ y₁ y₂) ≠ 0) :
    phi hb' (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = phi hb' (.some x₁ y₁ h₁) + phi hb' (.some x₂ y₂ h₂) := by
  have hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve b).toAffine.negY x₂ y₂) := fun h => hx h.1
  have key := mul_addX_eq h₁ h₂ hxy
  have e₁ := (shortCurve_equation_iff b x₁ y₁).mp h₁.1
  have e₂ := (shortCurve_equation_iff b x₂ y₂).mp h₂.1
  have h₃ := nonsingular_add h₁ h₂ hxy
  have e₃ := (shortCurve_equation_iff b _ _).mp h₃.1
  rw [Point.add_of_X_ne hx, phi_some _ _ hx₃, phi_some _ _ hx₁, phi_some _ _ hx₂]
  simp only [Point.mk]
  set ℓ := (shortCurve b).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  set x₃ := (shortCurve b).toAffine.addX x₁ x₂ ℓ with hx₃def
  have hℓ : ℓ * (x₁ - x₂) = y₁ - y₂ := by
    rw [hℓdef, Affine.slope_of_X_ne hx]; field_simp [sub_ne_zero.mpr hx]
  have V1 : x₁ + x₂ + x₃ = ℓ ^ 2 := by
    simp only [hx₃def, Affine.addX, shortCurve_a₁, shortCurve_a₂]; ring
  set ν := y₁ - ℓ * x₁ with hν
  have hy₁ : y₁ = ℓ * x₁ + ν := by rw [hν]; ring
  have hy₂ : y₂ = ℓ * x₂ + ν := by rw [hν]; linear_combination hℓ
  have hy₃ : (shortCurve b).toAffine.addY x₁ x₂ y₁ ℓ = -(ℓ * x₃ + ν) := by
    simp only [Affine.addY, Affine.negAddY, Affine.negY, shortCurve_a₁, shortCurve_a₃, hx₃def]
    ring
  have V3 : x₁ * x₂ * x₃ = ν ^ 2 := key
  have V2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = b - 2 * ℓ * ν := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hx)
    linear_combination e₁ - (y₁ + ℓ * x₁ + ν) * hy₁ - e₂ + (y₂ + ℓ * x₂ + ν) * hy₂ +
      (x₁ - x₂) * (x₁ + x₂) * V1
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [h0] at V3
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_eq_zero] at V3
    tauto
  have e₃' : (ℓ * x₃ + ν) ^ 2 = x₃ ^ 3 + b * x₃ := by rw [hy₃] at e₃; linear_combination e₃
  have hX : y₁ ^ 2 / x₁ ^ 2 ≠ y₂ ^ 2 / x₂ ^ 2 := by
    intro h
    rw [div_eq_div_iff (pow_ne_zero 2 hx₁) (pow_ne_zero 2 hx₂)] at h
    have : x₁ * x₂ * ((x₁ - x₂) * (x₁ * x₂ - b)) = 0 := by
      linear_combination h - x₂ ^ 2 * e₁ + x₁ ^ 2 * e₂
    rcases mul_eq_zero.mp this with h0 | h0
    · exact mul_ne_zero hx₁ hx₂ h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact hx (sub_eq_zero.mp h0)
    · exact hb (sub_eq_zero.mp h0)
  have hl₃ : (shortCurve b).toAffine.addY x₁ x₂ y₁ ℓ * (b - x₃ ^ 2) / x₃ ^ 2 =
      -((b / ν - ℓ) * ((shortCurve b).toAffine.addY x₁ x₂ y₁ ℓ ^ 2 / x₃ ^ 2) +
        (-ν - b * ℓ ^ 2 / ν)) := by
    rw [hy₃]
    have := mwPhi_line hx₃ hν0 (y := ℓ * x₃ + ν) rfl e₃'
    linear_combination -this
  have hs : y₁ ^ 2 / x₁ ^ 2 + y₂ ^ 2 / x₂ ^ 2 +
      (shortCurve b).toAffine.addY x₁ x₂ y₁ ℓ ^ 2 / x₃ ^ 2 = (b / ν - ℓ) ^ 2 := by
    rw [hy₃, neg_sq]
    rw [hy₁, hy₂]
    exact mwPhi_sum_sq hx₁ hx₂ hx₃ hν0 V1 V2 V3
  exact (mwAdd_of_line _ _ _ hX (mwPhi_line hx₁ hν0 hy₁ e₁) (mwPhi_line hx₂ hν0 hy₂ e₂)
    hl₃ hs).symm

include hb' in
/-- Additivity of `φ` for doubling, when `y ≠ 0` and `2P ≠ (0,0)`. -/
theorem mwPhi_double {x y : K} (h : (shortCurve b).toAffine.Nonsingular x y) (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hx₃ : (shortCurve b).toAffine.addX x x ((shortCurve b).toAffine.slope x x y y) ≠ 0) :
    phi hb' (.some x y h + .some x y h) = phi hb' (.some x y h) + phi hb' (.some x y h) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_isElliptic (b := b)
  have hy' : y ≠ (shortCurve b).toAffine.negY x y := by
    rw [shortCurve_negY]; intro h0; apply hy
    have : (2 : K) * y = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left h2
  have hxy : ¬(x = x ∧ y = (shortCurve b).toAffine.negY x y) := fun h => hy' h.2
  have key := mul_addX_eq h h hxy
  have e := (shortCurve_equation_iff b x y).mp h.1
  have h₃ := nonsingular_add h h hxy
  have e₃ := (shortCurve_equation_iff b _ _).mp h₃.1
  rw [Point.add_self_of_Y_ne hy', phi_some _ _ hx₃, phi_some _ _ hx]
  simp only [Point.mk]
  set ℓ := (shortCurve b).toAffine.slope x x y y with hℓdef
  set x₃ := (shortCurve b).toAffine.addX x x ℓ with hx₃def
  have ht : 2 * y * ℓ = 3 * x ^ 2 + b := by
    rw [hℓdef, Affine.slope_of_Y_ne rfl hy']
    simp only [Affine.negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄,
      zero_mul, mul_zero, add_zero, sub_zero]
    rw [show y - -y = 2 * y by ring]
    exact mul_div_cancel₀ _ (mul_ne_zero h2 hy)
  have V1 : x + x + x₃ = ℓ ^ 2 := by
    simp only [hx₃def, Affine.addX, shortCurve_a₁, shortCurve_a₂]; ring
  set ν := y - ℓ * x with hν
  have hy₁ : y = ℓ * x + ν := by rw [hν]; ring
  have hy₃ : (shortCurve b).toAffine.addY x x y ℓ = -(ℓ * x₃ + ν) := by
    simp only [Affine.addY, Affine.negAddY, Affine.negY, shortCurve_a₁, shortCurve_a₃, hx₃def]
    ring
  have V3 : x * x * x₃ = ν ^ 2 := key
  have V2 : x * x + x * x₃ + x * x₃ = b - 2 * ℓ * ν := by
    linear_combination ht - 2 * ℓ * hy₁ + 2 * x * V1
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [h0] at V3
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_eq_zero] at V3
    tauto
  have hx3eq : x₃ * (2 * y) ^ 2 = (x ^ 2 - b) ^ 2 := by
    have : x₃ = ℓ ^ 2 - 2 * x := by linear_combination V1
    rw [this]
    linear_combination (2 * y * ℓ + 3 * x ^ 2 + b) * ht - 8 * x * e
  have hxb : b - x ^ 2 ≠ 0 := by
    intro h0
    have : x₃ * (2 * y) ^ 2 = 0 := by rw [hx3eq]; linear_combination (b - x ^ 2) * h0
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hx₃ h1
    · exact pow_ne_zero 2 (mul_ne_zero h2 hy) h1
  have e₃' : (ℓ * x₃ + ν) ^ 2 = x₃ ^ 3 + b * x₃ := by rw [hy₃] at e₃; linear_combination e₃
  have hY : y * (b - x ^ 2) / x ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hy hxb) (pow_ne_zero 2 hx)
  have ht' : (b / ν - ℓ) * (2 * (y * (b - x ^ 2) / x ^ 2)) = 3 * (y ^ 2 / x ^ 2) ^ 2 + b' := by
    rw [hb']
    exact mwPhi_tangent hx hν0 hy₁ e ht
  have hl₃ : (shortCurve b).toAffine.addY x x y ℓ * (b - x₃ ^ 2) / x₃ ^ 2 =
      -((b / ν - ℓ) * ((shortCurve b).toAffine.addY x x y ℓ ^ 2 / x₃ ^ 2) +
        (-ν - b * ℓ ^ 2 / ν)) := by
    rw [hy₃]
    have := mwPhi_line hx₃ hν0 (y := ℓ * x₃ + ν) rfl e₃'
    linear_combination -this
  have hs : y ^ 2 / x ^ 2 + y ^ 2 / x ^ 2 +
      (shortCurve b).toAffine.addY x x y ℓ ^ 2 / x₃ ^ 2 = (b / ν - ℓ) ^ 2 := by
    rw [hy₃, neg_sq]
    rw [hy₁]
    exact mwPhi_sum_sq hx hx hx₃ hν0 V1 V2 V3
  exact (mwDouble_of_line _ _ h2 hY ht' (mwPhi_line hx hν0 hy₁ e) hl₃ hs).symm

include hb' in
/-- Doubling, at group level: for `R ∉ {O, (0,0)}` with `2R ∉ {O, (0,0)}`. -/
theorem mwPhi_double' (R : (shortCurve b).toAffine.Point) (hR0 : R ≠ 0) (hRT : R ≠ tZero)
    (h2R0 : R + R ≠ 0) (h2RT : R + R ≠ tZero) : phi hb' (R + R) = phi hb' R + phi hb' R := by
  rcases R with _ | ⟨x, y, h⟩
  · exact absurd rfl hR0
  have hx : x ≠ 0 := fun hx => hRT (some_eq_tZero h hx)
  have hy : y ≠ 0 := fun hy =>
    h2R0 (Point.add_self_of_Y_eq (by rw [shortCurve_negY, hy, neg_zero]))
  have hy' : y ≠ (shortCurve b).toAffine.negY x y := by
    intro h0; apply h2R0; exact Point.add_self_of_Y_eq h0
  have hx₃ : (shortCurve b).toAffine.addX x x ((shortCurve b).toAffine.slope x x y y) ≠ 0 :=
    fun h0 => h2RT (by rw [Point.add_self_of_Y_ne hy']; exact some_eq_tZero _ h0)
  exact mwPhi_double hb' h hx hy hx₃

include hb' in
/-- **The two-isogeny is additive**: `φ(P + Q) = φ(P) + φ(Q)`. -/
theorem mwPhi_add (P Q : (shortCurve b).toAffine.Point) :
    phi hb' (P + Q) = phi hb' P + phi hb' Q := by
  by_cases hP0 : P = 0
  · rw [hP0, zero_add, phi_zero, zero_add]
  by_cases hQ0 : Q = 0
  · rw [hQ0, add_zero, phi_zero, add_zero]
  by_cases hPT : P = tZero
  · rw [hPT, add_comm, mwPhi_add_tZero, mwPhi_tZero, zero_add]
  by_cases hQT : Q = tZero
  · rw [hQT, mwPhi_add_tZero, mwPhi_tZero, add_zero]
  by_cases hS0 : P + Q = 0
  · have hQ : Q = -P := (neg_eq_of_add_eq_zero_right hS0).symm
    rw [hS0, phi_zero, hQ, mwPhi_neg, add_neg_cancel]
  by_cases hST : P + Q = tZero
  · have hQ : Q = -P + tZero := by rw [← hST]; abel
    rw [hST, mwPhi_tZero, hQ, mwPhi_add_tZero, mwPhi_neg, add_neg_cancel]
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd rfl hP0
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hQ0
  have hx₁ : x₁ ≠ 0 := fun hx => hPT (some_eq_tZero h₁ hx)
  have hx₂ : x₂ ≠ 0 := fun hx => hQT (some_eq_tZero h₂ hx)
  by_cases hx : x₁ = x₂
  · rcases (Point.X_eq_iff (h₁ := h₁) (h₂ := h₂)).mp hx with hPQ | hPQ
    · rw [← hPQ] at hS0 hST ⊢
      exact mwPhi_double' hb' _ hP0 hPT hS0 hST
    · exact absurd (by rw [hPQ, neg_add_cancel]) hS0
  by_cases hb : x₁ * x₂ = b
  · obtain ⟨h', e⟩ := mwAdd_tZero_some h₁ hx₁
    have hx' : b / x₁ = x₂ := by rw [div_eq_iff hx₁, ← hb]; ring
    rcases (Point.X_eq_iff (h₁ := h') (h₂ := h₂)).mp hx' with hPQ | hPQ
    · rw [← e] at hPQ
      rw [← hPQ, show Point.some x₁ y₁ h₁ + (Point.some x₁ y₁ h₁ + tZero) =
        (Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁) + tZero by abel, mwPhi_add_tZero,
        mwPhi_add_tZero]
      refine mwPhi_double' hb' _ hP0 hPT ?_ ?_
      · intro h0; apply hST; rw [← hPQ, ← add_assoc, h0, zero_add]
      · intro h0; apply hS0; rw [← hPQ, ← add_assoc, h0, mwTZero_add_tZero]
    · exfalso; apply hST
      rw [← e] at hPQ
      have hQ : Point.some x₂ y₂ h₂ = -(Point.some x₁ y₁ h₁ + tZero) := by rw [hPQ, neg_neg]
      rw [hQ, neg_add, ← add_assoc, add_neg_cancel, zero_add, mwNeg_tZero]
  have hx₃ : (shortCurve b).toAffine.addX x₁ x₂ ((shortCurve b).toAffine.slope x₁ x₂ y₁ y₂) ≠ 0 :=
    fun h0 => hST (by rw [Point.add_of_X_ne hx]; exact some_eq_tZero _ h0)
  exact mwPhi_add_generic hb' h₁ h₂ hx₁ hx₂ hx hb hx₃

/-- The two-isogeny as a homomorphism. -/
noncomputable def mwPhiHom : (shortCurve b).toAffine.Point →+ (shortCurve b').toAffine.Point where
  toFun := phi hb'
  map_zero' := rfl
  map_add' := mwPhi_add hb'

@[simp] theorem mwPhiHom_apply (P : (shortCurve b).toAffine.Point) :
    mwPhiHom hb' P = phi hb' P := rfl

end Phi

end ZInQ.RouteK.Rank
