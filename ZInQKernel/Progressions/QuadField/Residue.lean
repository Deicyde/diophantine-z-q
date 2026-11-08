/-
Plan step 3.5 (residue bound): the residue of the Dedekind zeta function of `ℚ(√d)` at `s = 1`
is at least `log ((1 + √5) / 2) / (6 √|d|)`.
-/
import ZInQKernel.Progressions.QuadField.Discriminant
import ZInQKernel.Progressions.QuadField.Regulator
import ZInQKernel.Progressions.QuadField.Torsion

namespace ZInQ.Progressions

open NumberField NumberField.InfinitePlace NumberField.Units

variable {d : ℤ} [Fact (¬ IsSquare (d : ℚ))]

/-- `log ((1 + √5) / 2) < 1`. -/
theorem log_golden_lt_one : Real.log ((1 + √5) / 2) < 1 := by
  have h5 : √5 < 3 := by
    rw [show (3 : ℝ) = √(3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have := Real.log_le_sub_one_of_pos (x := (1 + √5) / 2) (by positivity)
  linarith

theorem log_golden_pos : 0 < Real.log ((1 + √5) / 2) := by
  apply Real.log_pos
  have : 1 < √5 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- **Residue bound.** The residue at `s = 1` of the Dedekind zeta function of `ℚ(√d)` is at least
`log ((1 + √5) / 2) / (6 √|d|)`. -/
theorem dedekindZeta_residue_ge :
    Real.log ((1 + √5) / 2) / (6 * √|(d : ℝ)|) ≤ dedekindZeta_residue (Qsqrt d) := by
  have hd0 : d ≠ 0 := Qsqrt.ne_zero
  have hsd : 0 < √|(d : ℝ)| := Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast hd0))
  have hlog := log_golden_pos
  -- the denominator
  have hdisc : √|(discr (Qsqrt d) : ℝ)| ≤ 2 * √|(d : ℝ)| := by
    have h : |(discr (Qsqrt d) : ℝ)| ≤ 4 * |(d : ℝ)| := by exact_mod_cast Qsqrt.abs_discr_le
    calc √|(discr (Qsqrt d) : ℝ)| ≤ √(4 * |(d : ℝ)|) := Real.sqrt_le_sqrt h
      _ = 2 * √|(d : ℝ)| := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
  have hw : (torsionOrder (Qsqrt d) : ℝ) ≤ 6 := by exact_mod_cast Qsqrt.torsionOrder_le_six
  have hden_pos : 0 < (torsionOrder (Qsqrt d) : ℝ) * √|(discr (Qsqrt d) : ℝ)| := by
    have := torsionOrder_pos (Qsqrt d)
    have := discr_ne_zero (Qsqrt d)
    positivity
  have hden : (torsionOrder (Qsqrt d) : ℝ) * √|(discr (Qsqrt d) : ℝ)| ≤ 12 * √|(d : ℝ)| := by
    calc (torsionOrder (Qsqrt d) : ℝ) * √|(discr (Qsqrt d) : ℝ)|
        ≤ 6 * (2 * √|(d : ℝ)|) := mul_le_mul hw hdisc (Real.sqrt_nonneg _) (by norm_num)
      _ = 12 * √|(d : ℝ)| := by ring
  have hh : (1 : ℝ) ≤ classNumber (Qsqrt d) := by exact_mod_cast classNumber_pos (Qsqrt d)
  -- the numerator
  have hnum : 2 * Real.log ((1 + √5) / 2) ≤ 2 ^ nrRealPlaces (Qsqrt d) *
      (2 * Real.pi) ^ nrComplexPlaces (Qsqrt d) * regulator (Qsqrt d) * classNumber (Qsqrt d) := by
    rcases lt_or_gt_of_ne hd0 with hneg | hpos
    · rw [Qsqrt.nrRealPlaces_of_neg hneg, Qsqrt.nrComplexPlaces_of_neg hneg,
        Qsqrt.regulator_of_neg hneg]
      have := log_golden_lt_one
      have := Real.pi_gt_three
      nlinarith
    · rw [Qsqrt.nrRealPlaces_of_pos hpos, Qsqrt.nrComplexPlaces_of_pos hpos]
      have := Qsqrt.regulator_ge_of_pos hpos
      nlinarith
  rw [dedekindZeta_residue_def]
  calc Real.log ((1 + √5) / 2) / (6 * √|(d : ℝ)|)
      = 2 * Real.log ((1 + √5) / 2) / (12 * √|(d : ℝ)|) := by
        field_simp
        ring
    _ ≤ _ := div_le_div₀ (by linarith) hnum hden_pos hden

end ZInQ.Progressions
