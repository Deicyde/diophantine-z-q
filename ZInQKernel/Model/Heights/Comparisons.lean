import Mathlib

/-!
# Two explicit integer comparisons

Blueprint: `model/heights/height-comparisons.md`.

`41³ · 676 · 392³⁶ < 9¹⁰⁸` and `392 < 41³`, and their logarithmic forms
`log(41³·676)/108 + log 392/3 < log 9` and `log 392/3 < log 41`.
-/

namespace ZInQ

/-- The two integer comparisons (both sides of the first have about `104` digits). -/
theorem height_comparisons : 41 ^ 3 * 676 * 392 ^ 36 < 9 ^ 108 ∧ 392 < 41 ^ 3 := by
  constructor <;> norm_num

/-- `log(41³·676)/108 + log 392/3 < log 9`. -/
theorem log_height_comparison_one :
    Real.log (41 ^ 3 * 676) / 108 + Real.log 392 / 3 < Real.log 9 := by
  have h : ((41 : ℝ) ^ 3 * 676) * (392 : ℝ) ^ 36 < (9 : ℝ) ^ 108 := by norm_num
  have hl := Real.log_lt_log (by positivity) h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hl
  push_cast at hl
  generalize Real.log (41 ^ 3 * 676) = A at hl ⊢
  generalize Real.log 392 = B at hl ⊢
  linarith

/-- `log 392 / 3 < log 41`. -/
theorem log_height_comparison_two : Real.log 392 / 3 < Real.log 41 := by
  have h : (392 : ℝ) < (41 : ℝ) ^ 3 := by norm_num
  have hl := Real.log_lt_log (by positivity) h
  rw [Real.log_pow] at hl
  push_cast at hl
  linarith

end ZInQ
