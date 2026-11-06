import ZInQKernel.Model.Descent.FirstImage

/-!
# The second descent image is trivial

Blueprint: `model/descent/second-descent-image.md`.

On `E' = E_{4d²} : y² = x³ + 4 d² x` over `K₀` the Kummer map `α' = α_{4d²}` is trivial: every
abscissa `x ≠ 0` is totally positive, has even valuation at every prime (at `d` the odd case
`v_d(x) = 1` would make `-1` a square modulo `d`), hence is a totally positive unit times a
square, hence a square.
-/

namespace ZInQ

open QuadraticAlgebra K0 Descent WeierstrassCurve WeierstrassCurve.Affine

instance shortCurve_four_genD_sq_isElliptic : (shortCurve (4 * genD ^ 2)).IsElliptic :=
  shortCurve_isElliptic (mul_ne_zero (by norm_num) (pow_ne_zero 2 genD_ne_zero))

/-- A real `a ≠ 0` with `t² = a³ + c a`, `c > 0`, is positive. -/
theorem pos_of_sq_eq_cube_add {a c t : ℝ} (ha : a ≠ 0) (hc : 0 < c) (h : t ^ 2 = a ^ 3 + c * a) :
    0 < a := by
  by_contra hneg
  have ha' : a < 0 := lt_of_le_of_ne (not_lt.mp hneg) ha
  have : a * (a ^ 2 + c) < 0 := mul_neg_of_neg_of_pos ha' (by positivity)
  nlinarith [sq_nonneg t]

/-- Abscissas on `E'` are totally positive. -/
theorem totallyPositive_x_E' {x y : K0} (hx : x ≠ 0) (h : y ^ 2 = x ^ 3 + 4 * genD ^ 2 * x) :
    TotallyPositive x := by
  constructor
  · have := congrArg embPlus h
    simp only [map_pow, map_add, map_mul, map_ofNat] at this
    exact pos_of_sq_eq_cube_add (embPlus_ne_zero hx)
      (by have := embPlus_ne_zero genD_ne_zero; positivity) this
  · have := congrArg embMinus h
    simp only [map_pow, map_add, map_mul, map_ofNat] at this
    exact pos_of_sq_eq_cube_add (embMinus_ne_zero hx)
      (by have := embMinus_ne_zero genD_ne_zero; positivity) this

theorem vp_two_eq (π : Zs) : vp π 2 = 2 * vp π sqrt2 := by
  by_cases hπ : Prime π
  · rw [← sqrt2_sq, vp_pow hπ]; norm_num
  · simp [vp, hπ]

theorem vp_genDZ_four_genD_sq : vp genDZ (4 * genD ^ 2) = 2 := by
  rw [show (4 : K0) * genD ^ 2 = (2 * genD) ^ 2 by ring, vp_pow prime_genDZ,
    vp_mul prime_genDZ two_ne_zero genD_ne_zero, vp_genDZ_two, vp_genDZ_genD]
  norm_num

/-- The case `v_d(x) = 1` is impossible on `E'`. -/
theorem vp_genDZ_x_E'_ne_one {x y : K0} (hx : x ≠ 0) (h : y ^ 2 = x ^ 3 + 4 * genD ^ 2 * x) :
    vp genDZ x ≠ 1 := by
  intro h1
  set w := x / genD with hw
  have hw0 : w ≠ 0 := div_ne_zero hx genD_ne_zero
  have hvw : vp genDZ w = 0 := by
    rw [hw, vp_div prime_genDZ hx genD_ne_zero, h1, vp_genDZ_genD]; norm_num
  have hxw : x = genD * w := by have := genD_ne_zero; rw [hw]; field_simp
  have hpos := totallyPositive_x_E' hx h
  have hy : y ≠ 0 := by
    rintro rfl
    have := congrArg embPlus h
    simp only [map_pow, map_add, map_mul, map_ofNat, map_zero] at this
    have h1 := hpos.1
    have h2 := embPlus_ne_zero genD_ne_zero
    nlinarith [sq_nonneg (embPlus genD), mul_pos h1 (pow_pos h1 2)]
  have hw4 : w ^ 2 + 4 ≠ 0 := by
    intro h0
    apply hy
    have : y ^ 2 = genD ^ 3 * w * (w ^ 2 + 4) := by rw [h, hxw]; ring
    rw [h0, mul_zero] at this
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have e : y ^ 2 = genD ^ 3 * w * (w ^ 2 + 4) := by rw [h, hxw]; ring
  have := congrArg (vp genDZ) e
  rw [vp_pow prime_genDZ, vp_mul prime_genDZ (mul_ne_zero (pow_ne_zero 3 genD_ne_zero) hw0) hw4,
    vp_mul prime_genDZ (pow_ne_zero 3 genD_ne_zero) hw0, vp_pow prime_genDZ, vp_genDZ_genD, hvw,
    vp_sq_add_four_eq_zero hw0 hvw] at this
  push_cast at this
  omega

/-- Abscissas on `E'` have even valuation at every prime. -/
theorem even_vp_x_E' {x y : K0} (hx : x ≠ 0) (h : y ^ 2 = x ^ 3 + 4 * genD ^ 2 * x) {π : Zs}
    (hπ : Prime π) : Even (vp π x) := by
  have hB : (4 : K0) * genD ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 genD_ne_zero)
  have hk : vp π (4 * genD ^ 2) = 2 * (2 * vp π sqrt2 + vp π genD) := by
    rw [show (4 : K0) * genD ^ 2 = (2 * genD) ^ 2 by ring, vp_pow hπ,
      vp_mul hπ two_ne_zero genD_ne_zero, vp_two_eq]
    norm_num
  rcases even_vp_or_of_curve hπ hx hB h (by rw [hk]; exact even_two_mul _) with h1 | h1
  · exact h1
  rw [hk] at h1
  by_cases hd : Associated π genDZ
  · rw [vp_eq_of_associated hd] at h1 ⊢
    rw [vp_genDZ_sqrt2, vp_genDZ_genD] at h1
    exact absurd (by omega) (vp_genDZ_x_E'_ne_one hx h)
  · have : vp π genD = 0 := by rw [← toK0_genDZ]; exact vp_prime_eq_zero hπ prime_genDZ hd
    rw [this] at h1
    exact ⟨vp π sqrt2, by omega⟩

/-- **The second descent image is trivial**: `α_{4d²}(Q) = 1` for every `Q ∈ E'(K₀)`. -/
theorem kummer_E'_trivial (Q : (shortCurve (4 * genD ^ 2)).toAffine.Point) :
    kummer (4 * genD ^ 2) Q = 1 := by
  rcases Q with _ | ⟨x, y, hxy⟩
  · rfl
  by_cases hx : x = 0
  · subst hx
    rw [kummer_some_zero, show (4 : K0) * genD ^ 2 = (2 * genD) ^ 2 by ring, sqc_sq]
  rw [kummer_some_of_ne _ _ hx]
  have h := (shortCurve_equation_iff _ x y).mp hxy.1
  obtain ⟨u, e, z, he, hz, rfl⟩ :=
    eq_unit_mul_genD_pow_mul_sq hx fun π hπ _ => even_vp_x_E' hx h hπ
  have hu0 := toK0_ne_zero u.ne_zero
  -- `e = 0` since `v_d(x)` is even
  have hev := even_vp_x_E' hx h prime_genDZ
  rw [vp_mul prime_genDZ (mul_ne_zero hu0 (pow_ne_zero _ genD_ne_zero)) (pow_ne_zero 2 hz),
    vp_mul prime_genDZ hu0 (pow_ne_zero _ genD_ne_zero), vp_unit prime_genDZ, vp_pow prime_genDZ,
    vp_pow prime_genDZ, vp_genDZ_genD] at hev
  have he0 : e = 0 := by
    obtain ⟨k, hk⟩ := hev
    push_cast at hk
    omega
  subst he0
  rw [pow_zero, mul_one] at hx h ⊢
  -- the unit `u` is totally positive, hence a square
  have hpos := totallyPositive_x_E' hx h
  have hupos : TotallyPositive (Zs.toK0 u) := by
    have hz1 := embPlus_ne_zero hz
    have hz2 := embMinus_ne_zero hz
    obtain ⟨h1, h2⟩ := hpos
    simp only [map_mul, map_pow] at h1 h2
    exact ⟨pos_of_mul_pos_left h1 (by positivity), pos_of_mul_pos_left h2 (by positivity)⟩
  obtain ⟨w, hw⟩ := isSquare_of_totallyPositive_unit u hupos
  rw [hw, Units.val_pow_eq_pow_val, map_pow, ← mul_pow, sqc_sq]

end ZInQ
