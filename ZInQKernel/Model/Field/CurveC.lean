import ZInQKernel.Model.Field.Curve

/-!
# The curve `C`, the change of variables `θ : E ≃ C` and the point `R`

Blueprint: `model/descent/coordinate-change.md`, `model/descent/point-r-certificate.md`.

`C = curveC : y² = x³ - δ² x` with `δ = 3 - s`, `ε = 1 + s`. The map
`θ(x, y) = (ε⁴ x, ε⁶ y)` is the scaling isomorphism `scaleEquiv` with `u = ε²`, since
`-δ² = (ε²)⁴ (-d²)`. `R = (1 + s, 2 s) ∈ C(K₀)` and `θ⁻¹(2 R) = P₀`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

/-! ### Identities for `ε` and `δ` -/

theorem epsilon_ne_zero : epsilon ≠ 0 := by
  intro h; have := congrArg QuadraticAlgebra.re h; simp [epsilon] at this

/-- `ε⁻¹ = s - 1`. -/
theorem epsilon_mul_sqrt2_sub_one : epsilon * (sqrt2 - 1) = 1 := by
  ext <;> norm_num [epsilon, sqrt2]

theorem epsilon_inv : epsilon⁻¹ = sqrt2 - 1 :=
  inv_eq_of_mul_eq_one_right epsilon_mul_sqrt2_sub_one

/-- `N(ε) = -1`. -/
theorem norm_epsilon : QuadraticAlgebra.norm epsilon = -1 := by
  rw [K0.norm_eq]; simp [epsilon]; norm_num

theorem epsilon_sq : epsilon ^ 2 = ⟨3, 2⟩ := by
  ext <;> simp [epsilon, pow_succ] <;> norm_num

/-- `ε⁴ = 17 + 12 s`. -/
theorem epsilon_pow_four : epsilon ^ 4 = ⟨17, 12⟩ := by
  ext <;> simp [epsilon, pow_succ] <;> norm_num

/-- `ε⁶ = 99 + 70 s`. -/
theorem epsilon_pow_six : epsilon ^ 6 = ⟨99, 70⟩ := by
  ext <;> simp [epsilon, pow_succ] <;> norm_num

/-- `δ = ε⁴ d`. -/
theorem delta_eq_epsilon_pow_four_mul_genD : delta = epsilon ^ 4 * genD := by
  rw [epsilon_pow_four]; ext <;> simp [delta, genD] <;> norm_num

/-- `δ² = 11 - 6 s`. -/
theorem delta_sq : delta ^ 2 = ⟨11, -6⟩ := by
  ext <;> simp [delta, pow_two] <;> norm_num

theorem delta_ne_zero : delta ≠ 0 := by
  intro h; have := congrArg QuadraticAlgebra.re h; simp [delta] at this

/-- `-δ² = (ε²)⁴ (-d²)`: the scaling relation between `C` and `E`. -/
theorem neg_delta_sq_eq : -delta ^ 2 = (epsilon ^ 2) ^ 4 * -genD ^ 2 := by
  rw [delta_eq_epsilon_pow_four_mul_genD]; ring

/-! ### The curve `C` -/

/-- The curve `C : y² = x³ - δ² x` over `K₀`. -/
def curveC : WeierstrassCurve K0 := shortCurve (-delta ^ 2)

theorem curveC_equation_iff (x y : K0) :
    curveC.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - delta ^ 2 * x := by
  rw [curveC, shortCurve_equation_iff]; ring_nf

instance curveC_isElliptic : curveC.IsElliptic :=
  shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero 2 delta_ne_zero))

instance shortCurve_neg_delta_sq_isElliptic : (shortCurve (-delta ^ 2)).IsElliptic :=
  curveC_isElliptic

theorem curveC_equation_zero : curveC.toAffine.Equation 0 0 := by
  rw [curveC_equation_iff]; ring

theorem curveC_equation_delta : curveC.toAffine.Equation delta 0 := by
  rw [curveC_equation_iff]; ring

theorem curveC_equation_neg_delta : curveC.toAffine.Equation (-delta) 0 := by
  rw [curveC_equation_iff]; ring

/-- The two-torsion point `(0, 0)` of `C`. -/
def cT0 : curveC.toAffine.Point := Point.mk curveC_equation_zero
/-- The two-torsion point `(δ, 0)` of `C`. -/
def cTdelta : curveC.toAffine.Point := Point.mk curveC_equation_delta
/-- The two-torsion point `(-δ, 0)` of `C`. -/
def cTnegdelta : curveC.toAffine.Point := Point.mk curveC_equation_neg_delta

/-- `C(K₀)[2] = {O, (0,0), (δ,0), (-δ,0)}`. -/
theorem curveC_two_torsion (P : curveC.toAffine.Point) :
    2 • P = 0 ↔ P = 0 ∨ P = cT0 ∨ P = cTdelta ∨ P = cTnegdelta := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Point.zero_def]
  · refine (shortCurve_two_nsmul_some_eq_zero_iff (A := -delta ^ 2) h).trans ?_
    simp only [cT0, cTdelta, cTnegdelta, Point.mk, reduceCtorEq, false_or]
    have he := (shortCurve_equation_iff _ x y).mp h.1
    constructor
    · rintro rfl
      have : x * (x - delta) * (x + delta) = 0 := by linear_combination -he
      rcases mul_eq_zero.mp this with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · left; simp only [Point.some.injEq]; exact ⟨h2, trivial⟩
        · right; left; simp only [Point.some.injEq]; exact ⟨sub_eq_zero.mp h2, trivial⟩
      · right; right; simp only [Point.some.injEq]; exact ⟨eq_neg_of_add_eq_zero_left h1, trivial⟩
    · rintro (h1 | h1 | h1) <;> simp only [Point.some.injEq] at h1 <;> exact h1.2

/-! ### The change of variables `θ` -/

theorem epsilon_sq_ne_zero : epsilon ^ 2 ≠ 0 := pow_ne_zero 2 epsilon_ne_zero

/-- The isomorphism of groups `θ : E(K₀) ≃+ C(K₀)`, `O ↦ O`, `(x, y) ↦ (ε⁴ x, ε⁶ y)`. -/
def theta : genCurve.toAffine.Point ≃+ curveC.toAffine.Point :=
  scaleEquiv (A := -genD ^ 2) (B := -delta ^ 2) epsilon_sq_ne_zero neg_delta_sq_eq

theorem curveC_nonsingular_theta {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    curveC.toAffine.Nonsingular (epsilon ^ 4 * x) (epsilon ^ 6 * y) := by
  have := shortCurve_nonsingular_scale (A := -genD ^ 2) (B := -delta ^ 2) epsilon_sq_ne_zero
    neg_delta_sq_eq h
  rwa [← pow_mul, ← pow_mul] at this

theorem genCurve_nonsingular_theta_symm {x y : K0} (h : curveC.toAffine.Nonsingular x y) :
    genCurve.toAffine.Nonsingular (epsilon⁻¹ ^ 4 * x) (epsilon⁻¹ ^ 6 * y) := by
  have := shortCurve_nonsingular_scale (A := -delta ^ 2) (B := -genD ^ 2) (u := (epsilon ^ 2)⁻¹)
    (inv_ne_zero epsilon_sq_ne_zero)
    (by rw [neg_delta_sq_eq, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 4 epsilon_sq_ne_zero),
      one_mul]) h
  convert this using 2 <;> first | rfl | ring

@[simp] theorem theta_zero : theta 0 = 0 := rfl

theorem theta_some {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    theta (.some x y h) = .some _ _ (curveC_nonsingular_theta h) := by
  exact scaleEquiv_some_eq (A := -genD ^ 2) (B := -delta ^ 2) _ _ h _ (by ring) (by ring)

theorem theta_symm_some {x y : K0} (h : curveC.toAffine.Nonsingular x y) :
    theta.symm (.some x y h) = .some _ _ (genCurve_nonsingular_theta_symm h) := by
  rw [AddEquiv.symm_apply_eq, theta_some]
  simp only [Point.some.injEq]
  constructor <;> rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ epsilon_ne_zero, one_pow, one_mul]

/-- `θ` maps `E(K₀)[2]` onto `C(K₀)[2]`. -/
theorem theta_genT0 : theta genT0 = cT0 := by
  simp only [genT0, cT0, Point.mk, theta_some, mul_zero]

theorem theta_genTd : theta genTd = cTdelta := by
  simp only [genTd, cTdelta, Point.mk, theta_some, mul_zero, ← delta_eq_epsilon_pow_four_mul_genD]

theorem theta_genTnegd : theta genTnegd = cTnegdelta := by
  simp only [genTnegd, cTnegdelta, Point.mk, theta_some, mul_zero, mul_neg,
    ← delta_eq_epsilon_pow_four_mul_genD]

theorem two_nsmul_theta_eq_zero_iff (P : genCurve.toAffine.Point) :
    2 • theta P = 0 ↔ 2 • P = 0 := by
  rw [← map_nsmul, AddEquivClass.map_eq_zero_iff]

/-! ### The point `R = (1 + s, 2 s)` on `C` -/

/-- `(2s)² = (1 + s)³ - δ² (1 + s)`. -/
theorem pointR_curve : (2 * sqrt2) ^ 2 = epsilon ^ 3 - delta ^ 2 * epsilon := by
  rw [delta_sq]; ext <;> simp [epsilon, sqrt2, pow_succ] <;> norm_num

theorem two_sqrt2_ne_zero : 2 * sqrt2 ≠ 0 := mul_ne_zero two_ne_zero sqrt2_ne_zero

theorem pointR_equation : curveC.toAffine.Equation epsilon (2 * sqrt2) :=
  (curveC_equation_iff _ _).mpr pointR_curve

/-- The point `R = (1 + s, 2 s)` of `C(K₀)`. -/
def pointR : curveC.toAffine.Point := Point.mk pointR_equation

/-- The abscissa `(57 - 28 s)/8` of `2R`. -/
def twoRX : K0 := ⟨57 / 8, -7 / 2⟩
/-- The ordinate `(-660 + 417 s)/32` of `2R`. -/
def twoRY : K0 := ⟨-165 / 8, 417 / 32⟩

theorem twoRX_eq : twoRX = (57 - 28 * sqrt2) / 8 := by
  rw [eq_div_iff (by norm_num)]; ext <;> norm_num [twoRX, sqrt2]

theorem twoRY_eq : twoRY = (-660 + 417 * sqrt2) / 32 := by
  rw [eq_div_iff (by norm_num)]; ext <;> norm_num [twoRY, sqrt2]

/-- The tangent slope at `R` is `(3(1+s)² - δ²)/(2·2s) = (12 - s)/4`. -/
theorem pointR_slope : (3 * epsilon ^ 2 - delta ^ 2) / (2 * (2 * sqrt2)) = ⟨3, -1 / 4⟩ := by
  rw [div_eq_iff (mul_ne_zero two_ne_zero two_sqrt2_ne_zero), delta_sq]
  ext <;> simp [epsilon, sqrt2, pow_succ] <;> norm_num

theorem twoR_x : (⟨3, -1 / 4⟩ : K0) ^ 2 - 2 * epsilon = twoRX := by
  ext <;> simp [twoRX, epsilon, pow_succ] <;> norm_num

theorem twoR_y : (⟨3, -1 / 4⟩ : K0) * (epsilon - twoRX) - 2 * sqrt2 = twoRY := by
  ext <;> simp [twoRX, twoRY, epsilon, sqrt2] <;> norm_num

theorem twoR_equation : curveC.toAffine.Equation twoRX twoRY := by
  rw [curveC_equation_iff, delta_sq]
  ext <;> simp [twoRX, twoRY, pow_succ] <;> norm_num

theorem twoR_nonsingular : curveC.toAffine.Nonsingular twoRX twoRY :=
  equation_iff_nonsingular.mp twoR_equation

/-- `[2]R = ((57 - 28 s)/8, (-660 + 417 s)/32)`. -/
theorem two_smul_pointR : 2 • pointR = .some twoRX twoRY twoR_nonsingular := by
  have hy : 2 * sqrt2 ≠ curveC.toAffine.negY epsilon (2 * sqrt2) := by
    rw [curveC, shortCurve_negY]
    intro h
    apply two_sqrt2_ne_zero
    linear_combination h / 2
  rw [two_nsmul, pointR, Point.mk, Point.add_self_of_Y_ne hy]
  have hslope : curveC.toAffine.slope epsilon epsilon (2 * sqrt2) (2 * sqrt2) = ⟨3, -1 / 4⟩ := by
    rw [Affine.slope_of_Y_ne rfl hy, ← pointR_slope]
    simp only [curveC, shortCurve_negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₄]
    congr 1 <;> ring
  simp only [Point.some.injEq, Affine.addY, Affine.negAddY, Affine.addX, hslope]
  simp only [curveC, shortCurve_negY, shortCurve_a₁, shortCurve_a₂]
  constructor
  · rw [← twoR_x]; ring
  · rw [← twoR_y, ← twoR_x]; ring

/-- `ε⁴ x₀ = (57 - 28 s)/8`, i.e. `ε⁻⁴ (57 - 28 s)/8 = (1641 - 1160 s)/8`. -/
theorem epsilon_pow_four_mul_genX0 : epsilon ^ 4 * genX0 = twoRX := by
  rw [epsilon_pow_four]; ext <;> simp [genX0, twoRX] <;> norm_num

/-- `ε⁶ y₀ = (-660 + 417 s)/32`, i.e. `ε⁻⁶ (-660 + 417 s)/32 = (-123720 + 87483 s)/32`. -/
theorem epsilon_pow_six_mul_genY0 : epsilon ^ 6 * genY0 = twoRY := by
  rw [epsilon_pow_six]; ext <;> simp [genY0, twoRY] <;> norm_num

theorem epsilon_inv_pow_four_mul_twoRX : epsilon⁻¹ ^ 4 * twoRX = genX0 := by
  rw [← epsilon_pow_four_mul_genX0, inv_pow, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 4 epsilon_ne_zero), one_mul]

theorem epsilon_inv_pow_six_mul_twoRY : epsilon⁻¹ ^ 6 * twoRY = genY0 := by
  rw [← epsilon_pow_six_mul_genY0, inv_pow, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 6 epsilon_ne_zero), one_mul]

/-- `θ(P₀) = 2R`. -/
theorem theta_genP0 : theta genP0 = 2 • pointR := by
  rw [two_smul_pointR, genP0, Point.mk, theta_some]
  simp only [Point.some.injEq]
  exact ⟨epsilon_pow_four_mul_genX0, epsilon_pow_six_mul_genY0⟩

/-- `θ⁻¹(2R) = P₀`. -/
theorem theta_symm_two_smul_pointR : theta.symm (2 • pointR) = genP0 := by
  rw [AddEquiv.symm_apply_eq, theta_genP0]

end ZInQ
