import ZInQKernel.Compiler.Precision.ZCoordinate
import ZInQKernel.Assembly.Real.Derivative
import ZInQKernel.Multiplication.Local.FormalGroup
import ZInQKernel.Model.DivisionPolynomials.Classical

/-!
# Bridges between the chapters

* `Syntax.WA A` (division polynomials) and `shortCurve A` (model field) are the same curve.
* The three definitions of `z = -x/y`: `Compiler.Precision.zPt`, `Assembly.zCoord` and
  `Mult.zCoord`.
* The real embeddings of `u + v s` are `u ± v √2`; consequently
  `ε_l = |re z_l| + |im z_l| ≤ |σ₊ z_l| + |σ₋ z_l|` and
  `r(a, j) = (σ₊ + σ₋)(z_j / z_a) / 2`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

/-! ### The curve `y² = x³ + A x` -/

/-- `W_A` of the division-polynomial chapter is `shortCurve A` of the model chapter. -/
theorem WA_eq_shortCurve {F : Type*} [Field F] (A : F) : Syntax.WA A = shortCurve A := rfl

/-! ### The coordinate `z` -/

/-- `zPt` (precision chapter) is `Assembly.zCoord` (real approximation). -/
theorem zPt_eq_assembly_zCoord : Compiler.Precision.zPt = Assembly.zCoord := by
  funext P; cases P <;> rfl

/-- `zPt` (precision chapter) is `Mult.zCoord` (multiplication chapter) on `E(K₀)`. -/
theorem zPt_eq_mult_zCoord (P : genCurve.toAffine.Point) :
    Compiler.Precision.zPt P = Mult.zCoord (A := -genD ^ 2) P := by
  cases P <;> rfl

/-- `Assembly.zCoord` is `Mult.zCoord` on `E(K₀)`. -/
theorem assembly_zCoord_eq_mult_zCoord (P : genCurve.toAffine.Point) :
    Assembly.zCoord P = Mult.zCoord (A := -genD ^ 2) P := by
  cases P <;> rfl

/-! ### The real embeddings -/

namespace K0

/-- `σ₊(u + v s) = u + v √2`. -/
theorem embPlus_mk (u v : ℚ) : embPlus ⟨u, v⟩ = (u : ℝ) + v * Real.sqrt 2 := embPlus_apply _

/-- `σ₋(u + v s) = u - v √2`. -/
theorem embMinus_mk (u v : ℚ) : embMinus ⟨u, v⟩ = (u : ℝ) - v * Real.sqrt 2 := embMinus_apply _

/-- `σ₊(u + v s) = u + v √2`, with `u + v s` written in `K₀`. -/
theorem embPlus_add_mul_sqrt2 (u v : ℚ) :
    embPlus ((u : K0) + (v : K0) * sqrt2) = (u : ℝ) + v * Real.sqrt 2 := by
  rw [embPlus_apply]; simp [sqrt2]

/-- `σ₋(u + v s) = u - v √2`, with `u + v s` written in `K₀`. -/
theorem embMinus_add_mul_sqrt2 (u v : ℚ) :
    embMinus ((u : K0) + (v : K0) * sqrt2) = (u : ℝ) - v * Real.sqrt 2 := by
  rw [embMinus_apply]; simp [sqrt2]

/-- `|re z| + |im z| ≤ |σ₊ z| + |σ₋ z|`. -/
theorem abs_re_add_abs_im_le (z : K0) :
    (|z.re| + |z.im| : ℚ) ≤ |embPlus z| + |embMinus z| := by
  rw [embPlus_apply, embMinus_apply]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  set u : ℝ := (z.re : ℝ)
  set v : ℝ := (z.im : ℝ)
  have hv : |v| ≤ |v * Real.sqrt 2| := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt 2)]
    nlinarith [abs_nonneg v]
  have key : |u| + |v * Real.sqrt 2| ≤ |u + v * Real.sqrt 2| + |u - v * Real.sqrt 2| := by
    rcases le_total |v * Real.sqrt 2| |u| with h | h
    · calc |u| + |v * Real.sqrt 2| ≤ |u| + |u| := by linarith
        _ = |(u + v * Real.sqrt 2) + (u - v * Real.sqrt 2)| := by
          rw [show u + v * Real.sqrt 2 + (u - v * Real.sqrt 2) = 2 * u by ring, abs_mul]
          norm_num; ring
        _ ≤ _ := abs_add_le _ _
    · calc |u| + |v * Real.sqrt 2| ≤ |v * Real.sqrt 2| + |v * Real.sqrt 2| := by linarith
        _ = |(u + v * Real.sqrt 2) - (u - v * Real.sqrt 2)| := by
          rw [show u + v * Real.sqrt 2 - (u - v * Real.sqrt 2) = 2 * (v * Real.sqrt 2) by ring,
            abs_mul]
          norm_num; ring
        _ ≤ _ := abs_sub _ _
  push_cast
  linarith

/-- `re z = (σ₊ z + σ₋ z) / 2`. -/
theorem re_eq_half_emb_sum (z : K0) : (z.re : ℝ) = (embPlus z + embMinus z) / 2 := by
  rw [embPlus_apply, embMinus_apply]; ring

end K0

namespace Compiler.Precision

/-- `ε_l = |re z_l| + |im z_l| ≤ |σ₊ z_l| + |σ₋ z_l|`. -/
theorem epsIdx_le_emb (l : ℤ) :
    (epsIdx l : ℝ) ≤ |K0.embPlus (zIdx l)| + |K0.embMinus (zIdx l)| := by
  have := K0.abs_re_add_abs_im_le (zIdx l)
  rw [epsIdx]; push_cast at this ⊢; exact this

/-- `r(a, j) = (σ₊ + σ₋)(z_j / z_a) / 2`. -/
theorem rRatio_eq_half_emb_sum (a j : ℤ) :
    (rRatio a j : ℝ) =
      (K0.embPlus (zIdx j / zIdx a) + K0.embMinus (zIdx j / zIdx a)) / 2 := by
  rw [rRatio, K0.re_eq_half_emb_sum]

end Compiler.Precision

end ZInQ
