import ZInQKernel.Model.Heights
import ZInQKernel.Multiplication.Soundness.RationalHeights

/-!
# Height bounds in `K₀`

Blueprint: `multiplication/soundness/field-height-bounds.md`.

`hK0` is half of Mathlib's relative height `logHeight₁` on `K₀`, whose infinite places have total
multiplicity `[K₀ : ℚ] = 2`; Mathlib's `logHeight₁_mul_le` and `logHeight₁_add_le` give (1). The
heights of `s` and `ε` come from the formula for the height of a fraction in `ℤ[s]`.
-/

namespace ZInQ.Mult

open Height

theorem totalWeight_K0 : totalWeight K0 = 2 := by
  rw [NumberField.totalWeight_eq_finrank, finrank_K0]

theorem hK0_mul_le (x y : K0) : hK0 (x * y) ≤ hK0 x + hK0 y := by
  have := logHeight₁_mul_le x y
  simp only [hK0]; linarith

theorem hK0_add_le (x y : K0) : hK0 (x + y) ≤ hK0 x + hK0 y + Real.log 2 := by
  have := logHeight₁_add_le x y
  rw [totalWeight_K0] at this
  simp only [hK0]; push_cast at this; linarith

theorem hK0_pow (x : K0) (n : ℕ) : hK0 (x ^ n) = n * hK0 x := by
  simp only [hK0, logHeight₁_pow]; ring

/-- On `ℚ ⊆ K₀` the height is the rational height. -/
theorem hK0_ratCast_eq_ratHeight (r : ℚ) : hK0 (r : K0) = ratHeight r := hK0_ratCast r

theorem sqrt2_eq_div : sqrt2 = Zs.toK0 sqrt2Z / Zs.toK0 1 := by
  rw [map_one, div_one, toK0_sqrt2Z]

theorem epsilon_eq_div : epsilon = Zs.toK0 epsilonZ / Zs.toK0 1 := by
  rw [map_one, div_one, toK0_epsilonZ]

/-- `h(s) = ½ log 2`. -/
theorem hK0_sqrt2 : hK0 sqrt2 = Real.log 2 / 2 := by
  rw [sqrt2_eq_div, hK0_div_of_isCoprime (isCoprime_one_right), map_one, map_one, map_one,
    toK0_sqrt2Z]
  have h1 := one_lt_sqrt_two
  simp only [K0.embPlus_apply, K0.embMinus_apply, sqrt2, Rat.cast_zero, Rat.cast_one, zero_add,
    zero_sub, one_mul, abs_one, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt 2),
    max_eq_left h1.le, Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- `h(ε) = ½ log(1 + √2)`. -/
theorem hK0_epsilon : hK0 epsilon = Real.log (1 + Real.sqrt 2) / 2 := by
  rw [epsilon_eq_div, hK0_div_of_isCoprime (isCoprime_one_right), map_one, map_one, map_one,
    toK0_epsilonZ]
  have h1 := one_lt_sqrt_two
  have h2 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  simp only [K0.embPlus_apply, K0.embMinus_apply, epsilon, Rat.cast_one, one_mul, abs_one,
    abs_of_pos (by linarith : (0 : ℝ) < 1 + Real.sqrt 2),
    abs_of_neg (by linarith : 1 - Real.sqrt 2 < 0)]
  rw [max_eq_left (by linarith), max_eq_right (by linarith), Real.log_one, add_zero]

/-- `h(ε⁴ x) ≤ h(x) + 2 log(1 + √2)`. -/
theorem hK0_epsilon_pow_four_mul_le (x : K0) :
    hK0 (epsilon ^ 4 * x) ≤ hK0 x + 2 * Real.log (1 + Real.sqrt 2) := by
  have := hK0_mul_le (epsilon ^ 4) x
  rw [hK0_pow, hK0_epsilon] at this
  push_cast at this; linarith

/-- `h(x₀ + x₁ s) ≤ h(x₀) + h(x₁) + ³⁄₂ log 2` for `x₀, x₁ ∈ ℚ`. -/
theorem hK0_ratCast_add_mul_sqrt2_le (x₀ x₁ : ℚ) :
    hK0 ((x₀ : K0) + (x₁ : K0) * sqrt2) ≤ ratHeight x₀ + ratHeight x₁ + 3 / 2 * Real.log 2 := by
  have h1 := hK0_add_le (x₀ : K0) ((x₁ : K0) * sqrt2)
  have h2 := hK0_mul_le (x₁ : K0) sqrt2
  rw [hK0_sqrt2, hK0_ratCast_eq_ratHeight] at h2
  rw [hK0_ratCast_eq_ratHeight] at h1
  linarith

/-- **Height bounds in `K₀`.** -/
theorem field_height_bounds :
    (∀ x y : K0, hK0 (x * y) ≤ hK0 x + hK0 y ∧ hK0 (x + y) ≤ hK0 x + hK0 y + Real.log 2) ∧
    (hK0 sqrt2 = Real.log 2 / 2 ∧ hK0 epsilon = Real.log (1 + Real.sqrt 2) / 2 ∧
      ∀ x : K0, hK0 (epsilon ^ 4 * x) ≤ hK0 x + 2 * Real.log (1 + Real.sqrt 2)) ∧
    (∀ x₀ x₁ : ℚ,
      hK0 ((x₀ : K0) + (x₁ : K0) * sqrt2) ≤ ratHeight x₀ + ratHeight x₁ + 3 / 2 * Real.log 2) :=
  ⟨fun x y => ⟨hK0_mul_le x y, hK0_add_le x y⟩,
    ⟨hK0_sqrt2, hK0_epsilon, hK0_epsilon_pow_four_mul_le⟩, hK0_ratCast_add_mul_sqrt2_le⟩

end ZInQ.Mult
