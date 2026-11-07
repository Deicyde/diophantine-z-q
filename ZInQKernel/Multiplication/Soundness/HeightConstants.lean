import Mathlib

/-!
# Explicit height constants

Blueprint: `multiplication/soundness/height-constant-integers.md` and
`multiplication/soundness/height-constants.md`.

The finite-box deduction uses two numerical constants: `B₀ < 10` and
`log 41 - ⅓ log 392 > 1`. Their numerical content is three inequalities between natural numbers,
checked by the kernel; the passage to the real statements uses `(1 + √2)¹² = 19601 + 13860 √2`
and `2.718 < e < 2.7183`.
-/

namespace ZInQ.Mult

/-- **The integer inequalities behind the height constants.** -/
theorem height_constants_int :
    3 ^ 24 * 2 ^ 9 * 39202 * 676 ^ 2 * 1000 ^ 60 < 2718 ^ 60 ∧
      392 * 27183 ^ 3 < 41 ^ 3 * 10 ^ 12 ∧ 2 * 13860 ^ 2 < 19601 ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The constant `B₀ = 4 log 3 + ³⁄₂ log 2 + 2 log(1 + √2) + ⅓ log 676`. -/
noncomputable def heightB0 : ℝ :=
  4 * Real.log 3 + 3 / 2 * Real.log 2 + 2 * Real.log (1 + Real.sqrt 2) + Real.log 676 / 3

/-- `(1 + √2)¹² = 19601 + 13860 √2`. -/
theorem one_add_sqrt_two_pow_twelve :
    (1 + Real.sqrt 2) ^ 12 = 19601 + 13860 * Real.sqrt 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set r := Real.sqrt 2
  have h2 : (1 + r) ^ 2 = 3 + 2 * r := by linear_combination h
  have h4 : (3 + 2 * r) ^ 2 = 17 + 12 * r := by linear_combination 4 * h
  rw [show (1 + r) ^ 12 = (((1 + r) ^ 2) ^ 2) ^ 3 by ring, h2, h4]
  linear_combination (7344 + 1728 * r) * h

/-- `(1 + √2)¹² < 39202`. -/
theorem one_add_sqrt_two_pow_twelve_lt : (1 + Real.sqrt 2) ^ 12 < 39202 := by
  rw [one_add_sqrt_two_pow_twelve]
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hi : (2 : ℝ) * 13860 ^ 2 < 19601 ^ 2 := by exact_mod_cast height_constants_int.2.2
  have : 13860 * Real.sqrt 2 < 19601 := by
    apply lt_of_pow_lt_pow_left₀ 2 (by norm_num)
    rw [mul_pow, h]; linarith
  linarith

/-- **Explicit height constants (1).** `B₀ < 10`. -/
theorem heightB0_lt_ten : heightB0 < 10 := by
  have hs : 0 < 1 + Real.sqrt 2 := by positivity
  -- `6 B₀ = log (3²⁴ · 2⁹ · (1 + √2)¹² · 676²)`.
  have h6 : 6 * heightB0 =
      Real.log ((3 : ℝ) ^ 24 * 2 ^ 9 * (1 + Real.sqrt 2) ^ 12 * 676 ^ 2) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow, heightB0]
    push_cast; ring
  have hi : (3 : ℝ) ^ 24 * 2 ^ 9 * 39202 * 676 ^ 2 * 1000 ^ 60 < 2718 ^ 60 := by
    exact_mod_cast height_constants_int.1
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hY : (3 : ℝ) ^ 24 * 2 ^ 9 * (1 + Real.sqrt 2) ^ 12 * 676 ^ 2 < Real.exp 60 := by
    calc (3 : ℝ) ^ 24 * 2 ^ 9 * (1 + Real.sqrt 2) ^ 12 * 676 ^ 2
        < 3 ^ 24 * 2 ^ 9 * 39202 * 676 ^ 2 := by
          gcongr; exact one_add_sqrt_two_pow_twelve_lt
      _ < (2.718 : ℝ) ^ 60 := by
          rw [show (2.718 : ℝ) ^ 60 = 2718 ^ 60 / 1000 ^ 60 by norm_num,
            lt_div_iff₀ (by positivity)]
          exact hi
      _ < Real.exp 1 ^ 60 := by gcongr
      _ = Real.exp 60 := by rw [← Real.exp_nat_mul]; norm_num
  have hl := Real.log_lt_log (by positivity) hY
  rw [Real.log_exp, ← h6] at hl
  linarith

/-- **Explicit height constants (2).** `log 41 - ⅓ log 392 > 1`. -/
theorem one_lt_log_41_sub : 1 < Real.log 41 - Real.log 392 / 3 := by
  have hi : (392 : ℝ) * 27183 ^ 3 < 41 ^ 3 * 10 ^ 12 := by
    exact_mod_cast height_constants_int.2.1
  have he : Real.exp 1 < (2.7183 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hY : 392 * Real.exp 3 < (41 : ℝ) ^ 3 := by
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    calc 392 * Real.exp 3 = 392 * Real.exp 1 ^ 3 := by rw [h3]
      _ < 392 * (2.7183 : ℝ) ^ 3 := by gcongr
      _ < (41 : ℝ) ^ 3 := by norm_num at hi ⊢
  have hl := Real.log_lt_log (by positivity) hY
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp, Real.log_pow] at hl
  push_cast at hl
  linarith

end ZInQ.Mult
