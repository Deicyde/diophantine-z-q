import ZInQKernel.Hypotheses.MordellWeil
import ZInQ.RationalPositiveGuard

/-!
# Inverse witnesses, positivity and absolute value over the rationals

* Inverses are equations `a w = 1`; for a pair `(a₀, a₁)` the norm `a₀² - 2a₁²` vanishes only at
  `(0, 0)`, so `a₀ + a₁ s ≠ 0` exactly when its norm has an inverse.
* A rational is positive exactly when it times a sum of four squares is `1`
  (Lagrange's four-square theorem).
* `a = |x|` exactly when `a` is a sum of four squares and `a² = x²`.
-/

namespace ZInQ.Syntax

/-! ### Inverse witnesses -/

/-- `a ≠ 0` exactly when some `w` satisfies `a w = 1`. -/
theorem exists_mul_eq_one_iff (a : ℚ) : (∃ w : ℚ, a * w = 1) ↔ a ≠ 0 := by
  constructor
  · rintro ⟨w, hw⟩ rfl
    simp at hw
  · intro ha
    exact ⟨a⁻¹, mul_inv_cancel₀ ha⟩

/-- An inverse witness is the inverse. -/
theorem eq_one_div_of_mul_eq_one {a w : ℚ} (h : a * w = 1) : w = 1 / a := by
  have ha : a ≠ 0 := (exists_mul_eq_one_iff a).1 ⟨w, h⟩
  field_simp
  linarith [mul_comm a w]

/-- The pair norm `a₀² - 2a₁²` vanishes only at `(0, 0)`, by the irrationality of `√2`. -/
theorem pairNorm_eq_zero_iff (a0 a1 : ℚ) : a0 ^ 2 - 2 * a1 ^ 2 = 0 ↔ a0 = 0 ∧ a1 = 0 := by
  constructor
  · intro h
    by_cases h1 : a1 = 0
    · subst h1
      refine ⟨?_, rfl⟩
      simpa using h
    · exfalso
      apply not_isSquare_two_rat
      refine ⟨a0 / a1, ?_⟩
      field_simp
      linarith
  · rintro ⟨rfl, rfl⟩
    ring

theorem pairNorm_ne_zero_iff (a0 a1 : ℚ) : a0 ^ 2 - 2 * a1 ^ 2 ≠ 0 ↔ (a0, a1) ≠ (0, 0) := by
  rw [Ne, pairNorm_eq_zero_iff, Ne, Prod.mk.injEq]

/-- `1, s` are linearly independent over `ℚ`: `a₀ + a₁ s = 0` exactly when `a₀ = a₁ = 0`. -/
theorem K0_mk_eq_zero_iff (a0 a1 : ℚ) : (⟨a0, a1⟩ : K0) = 0 ↔ a0 = 0 ∧ a1 = 0 := by
  constructor
  · intro h
    exact ⟨congrArg QuadraticAlgebra.re h, congrArg QuadraticAlgebra.im h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The element `a₀ + a₁ s` of `K₀`. -/
theorem K0_mk_eq (a0 a1 : ℚ) : (⟨a0, a1⟩ : K0) = (a0 : K0) + (a1 : K0) * sqrt2 := by
  ext <;> simp [sqrt2]

/-- **Inverse witnesses for pairs.** `a₀ + a₁ s ≠ 0` iff `a₀² - 2a₁² ≠ 0` iff the norm has an
inverse witness. -/
theorem K0_ne_zero_iff_pairNorm (a0 a1 : ℚ) :
    (⟨a0, a1⟩ : K0) ≠ 0 ↔ a0 ^ 2 - 2 * a1 ^ 2 ≠ 0 := by
  rw [Ne, K0_mk_eq_zero_iff, Ne, pairNorm_eq_zero_iff]

theorem exists_mul_pairNorm_eq_one_iff (a0 a1 : ℚ) :
    (∃ w : ℚ, (a0 ^ 2 - 2 * a1 ^ 2) * w = 1) ↔ (⟨a0, a1⟩ : K0) ≠ 0 := by
  rw [exists_mul_eq_one_iff, K0_ne_zero_iff_pairNorm]

/-! ### Positivity and absolute value -/

/-- **Strict positivity by four squares.** -/
theorem pos_iff_four_squares (s : ℚ) :
    0 < s ↔ ∃ z : Fin 4 → ℚ, s * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) = 1 := by
  rw [RationalGuards.rational_pos_iff_four_squares_inverse]
  simp only [Fin.sum_univ_four]

/-- A nonnegative rational is a sum of four rational squares. -/
theorem exists_four_squares_of_nonneg {r : ℚ} (hr : 0 ≤ r) :
    ∃ z : Fin 4 → ℚ, r = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 := by
  rcases hr.eq_or_lt with rfl | hr
  · exact ⟨0, by simp⟩
  · obtain ⟨z, hz⟩ := (pos_iff_four_squares r⁻¹).1 (inv_pos.2 hr)
    refine ⟨z, ?_⟩
    have := hr.ne'
    field_simp at hz
    linarith

/-- **Absolute value by four squares.** -/
theorem eq_abs_iff_four_squares (a x : ℚ) :
    a = |x| ↔ ∃ z : Fin 4 → ℚ, a = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 ∧ a ^ 2 = x ^ 2 := by
  constructor
  · rintro rfl
    obtain ⟨z, hz⟩ := exists_four_squares_of_nonneg (abs_nonneg x)
    exact ⟨z, hz, sq_abs x⟩
  · rintro ⟨z, hz, hsq⟩
    have ha : 0 ≤ a := by rw [hz]; positivity
    rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg ha] at hsq
    exact hsq

end ZInQ.Syntax
