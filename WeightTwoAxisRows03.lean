import WeightTwoTraceResidues02

/-!
# The actual one-dimensional axis series

The nonzero imaginary rows have an explicit summable geometric majorant
whose total tends to zero. Comparing the resulting row limit with the
independent second-theta-moment limit identifies the genuine real-axis
inverse-square series. Only one-dimensional row summation is used here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open Complex Filter ModularForm
open UpperHalfPlane hiding I
open scoped Topology Real ModularForm MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants

open ZInQ.Contrib.HeckePrimeRationality
open EisensteinWeightTwo

/-- The geometric decay radius of a nonzero imaginary row. -/
def rowRadius (τ : ℍ) : ℝ := Real.exp (-2 * Real.pi * τ.im)

/-- A fixed denominator bound valid above height one. -/
def rowBoundConstant : ℝ := 4 * Real.pi ^ 2 / (1 - Real.exp (-2 * Real.pi)) ^ 2

/-- The nonzero-row tail, with the real-axis row removed literally. -/
def rowTail (s : ℝ) (τ : ℍ) (m : ℤ) : ℂ :=
  if m = 0 then 0 else inverseSquareRow ((s : ℂ) + (m : ℂ) * (τ : ℂ))

lemma rowRadius_pos (τ : ℍ) : 0 < rowRadius τ := Real.exp_pos _

lemma rowRadius_lt_one (τ : ℍ) : rowRadius τ < 1 := by
  rw [rowRadius, Real.exp_lt_one_iff]
  nlinarith [Real.pi_pos, τ.im_pos]

lemma rowBoundConstant_nonneg : 0 ≤ rowBoundConstant := by
  unfold rowBoundConstant
  positivity

lemma row_norm_bound (s : ℝ) (τ : ℍ) (hy : 1 ≤ τ.im) (m : ℤ) (hm : m ≠ 0) :
    ‖inverseSquareRow ((s : ℂ) + (m : ℂ) * (τ : ℂ))‖ ≤
      rowBoundConstant * rowRadius τ ^ m.natAbs := by
  let w : ℂ := (s : ℂ) + (m : ℂ) * (τ : ℂ)
  have him : w.im = (m : ℝ) * τ.im := by simp [w, Complex.mul_im]
  have habs : |w.im| = (m.natAbs : ℝ) * τ.im := by
    rw [him, abs_mul, abs_of_pos τ.im_pos, Nat.cast_natAbs, Int.cast_abs]
  have hm1 : (1 : ℝ) ≤ m.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hm
  have hi : 1 ≤ |w.im| := by rw [habs]; nlinarith
  have hw : w.im ≠ 0 := by intro h; rw [h, abs_zero] at hi; norm_num at hi
  have hr : Real.exp (-2 * Real.pi) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hqr : Real.exp (-2 * Real.pi * |w.im|) ≤ Real.exp (-2 * Real.pi) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have h := inverseSquareRow_norm_le hw hr hqr
  have hp : Real.exp (-2 * Real.pi * |w.im|) = rowRadius τ ^ m.natAbs := by
    rw [rowRadius, ← Real.exp_nat_mul]
    congr 1
    rw [habs]
    ring
  simpa only [rowBoundConstant, hp] using h

/-- Both genuine summability and an explicit vanishing bound for the removed-row tail. -/
theorem rowTail_summable_bound (s : ℝ) (τ : ℍ) (hy : 1 ≤ τ.im) :
    Summable (rowTail s τ) ∧
      ‖∑' m : ℤ, rowTail s τ m‖ ≤
        2 * rowBoundConstant * rowRadius τ / (1 - rowRadius τ) := by
  let u : ℤ → ℝ := fun m => if m = 0 then 0 else rowBoundConstant * rowRadius τ ^ m.natAbs
  have hg := ThetaFive.hasSum_geom_natAbs rowBoundConstant (rowRadius_pos τ).le (rowRadius_lt_one τ)
  have hd := hasSum_ite_eq (0 : ℤ) rowBoundConstant
  have hu0 : HasSum u (rowBoundConstant / (1 - rowRadius τ) +
      rowBoundConstant * rowRadius τ / (1 - rowRadius τ) - rowBoundConstant) := by
    apply (hg.sub hd).congr_fun
    intro m
    by_cases hm : m = 0
    · simp [u, hm]
    · simp [u, hm]
  have hv : rowBoundConstant / (1 - rowRadius τ) +
      rowBoundConstant * rowRadius τ / (1 - rowRadius τ) - rowBoundConstant =
      2 * rowBoundConstant * rowRadius τ / (1 - rowRadius τ) := by
    field_simp [(sub_pos.mpr (rowRadius_lt_one τ)).ne']
    ring
  rw [hv] at hu0
  have hb (m : ℤ) : ‖rowTail s τ m‖ ≤ u m := by
    by_cases hm : m = 0
    · simp [rowTail, u, hm]
    · simpa only [rowTail, u, ite_eq_right hm] using row_norm_bound s τ hy m hm
  have hs : Summable (rowTail s τ) := Summable.of_norm_bounded hu0.summable hb
  exact ⟨hs, hs.hasSum.norm_le_of_bounded hu0 hb⟩

lemma rowRadius_tendsto : Tendsto rowRadius atImInfty (𝓝 0) := by
  have hy : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
  exact Real.tendsto_exp_atBot.comp (hy.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos]))

/-- The nonzero rows tend to zero, with the summability supplied rather than defaulted. -/
theorem rowTail_tendsto (s : ℝ) :
    Tendsto (fun τ : ℍ => ∑' m : ℤ, rowTail s τ m) atImInfty (𝓝 0) := by
  have hb : Tendsto (fun τ : ℍ => 2 * rowBoundConstant * rowRadius τ / (1 - rowRadius τ))
      atImInfty (𝓝 0) := by
    have h := (rowRadius_tendsto.const_mul (2 * rowBoundConstant)).div
      (tendsto_const_nhds.sub rowRadius_tendsto) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    change Tendsto (fun τ : ℍ => 2 * rowBoundConstant * rowRadius τ / (1 - rowRadius τ))
      atImInfty (𝓝 (2 * rowBoundConstant * 0 / (1 - 0))) at h
    simpa only [mul_zero, sub_zero, div_one] using h
  have hy : ∀ᶠ τ : ℍ in atImInfty, 1 ≤ τ.im :=
    (show Tendsto UpperHalfPlane.im atImInfty atTop from tendsto_comap).eventually (eventually_ge_atTop 1)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Filter.Eventually.of_forall fun τ => norm_nonneg _)
    (hy.mono fun τ hτ => (rowTail_summable_bound s τ hτ).2) hb

/-- The tail is the actual x-value plus G2 minus its literal real-axis row, on good axis labels. -/
theorem actual_axis_tail (N : ℕ) (hN : 0 < N) (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) (τ : ℍ) :
    (∑' m : ℤ, rowTail ((b : ℝ) / N) τ m) =
      TorsionWeierstrassData.xValue N 0 b τ + EisensteinSeries.G2 τ -
        inverseSquareRow ((b : ℂ) / (N : ℂ)) := by
  have hc : (((b : ℝ) / (N : ℝ) : ℝ) : ℂ) = (b : ℂ) / (N : ℂ) := by push_cast; rfl
  have h := hasSum_shifted_rows τ ((b : ℂ) / (N : ℂ))
  have ht : HasSum (rowTail ((b : ℝ) / N) τ)
      ((ThetaWeierstrass.periodPair τ).weierstrassP ((b : ℂ) / (N : ℂ)) + EisensteinSeries.G2 τ -
        inverseSquareRow ((b : ℂ) / (N : ℂ))) := by
    apply (h.sub (hasSum_ite_eq (0 : ℤ) (inverseSquareRow ((b : ℂ) / (N : ℂ))))).congr_fun
    intro m
    by_cases hm : m = 0
    · simp [rowTail, hm, inverseSquareRow]
    · simp only [rowTail, ite_eq_right hm, hc, sub_zero, inverseSquareRow]
  rw [TorsionWeierstrassData.xValue_of_good N 0 b τ (by simpa using hb)]
  have hp : CompletedTheta.torsionPoint N 0 b τ = (b : ℂ) / (N : ℂ) := by
    simp [CompletedTheta.torsionPoint]
  rw [hp]
  exact ht.tsum_eq

/-- The exact real-axis cotangent/cyclotomic identity follows from the actual two independent limits. -/
theorem inverseSquareRow_axis (N : ℕ) (hN : 0 < N) (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) :
    inverseSquareRow ((b : ℂ) / (N : ℂ)) =
      -4 * (Real.pi : ℂ) ^ 2 * Torsion.w N b / (1 - Torsion.w N b) ^ 2 := by
  have h1 := ((xValue_tendsto N hN 0 b).add G2_tendsto).sub_const
    (inverseSquareRow ((b : ℂ) / (N : ℂ)))
  have h2 : Tendsto (fun τ : ℍ => TorsionWeierstrassData.xValue N 0 b τ + EisensteinSeries.G2 τ -
      inverseSquareRow ((b : ℂ) / (N : ℂ))) atImInfty (𝓝 0) := by
    have he : (fun τ : ℍ => ∑' m : ℤ, rowTail ((b : ℝ) / N) τ m) =
        (fun τ : ℍ => TorsionWeierstrassData.xValue N 0 b τ + EisensteinSeries.G2 τ -
          inverseSquareRow ((b : ℂ) / (N : ℂ))) := funext (actual_axis_tail N hN b hb)
    rw [← he]
    exact rowTail_tendsto ((b : ℝ) / N)
  have h := tendsto_nhds_unique h1 h2
  rw [xConstant_axis N 0 b (dvd_zero _) hb, axisConstant] at h
  linear_combination -h

/-- Exact scaling of each term of the one-dimensional congruence series. -/
lemma axis_term_scaling (N : ℕ) (hN : 0 < N) (b n : ℤ) :
    1 / ((b : ℂ) / (N : ℂ) + (n : ℂ)) ^ 2 =
      (N : ℂ) ^ 2 * (1 / ((b : ℂ) + (N : ℂ) * (n : ℂ)) ^ 2) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [show (b : ℂ) / (N : ℂ) + (n : ℂ) =
    ((b : ℂ) + (N : ℂ) * (n : ℂ)) / (N : ℂ) by field_simp,
    div_pow, one_div, inv_div]
  ring

/-- Exact scaling between the torsion-axis row and the one-dimensional congruence series. -/
lemma inverseSquareRow_axis_scaling (N : ℕ) (hN : 0 < N) (b : ℤ) :
    inverseSquareRow ((b : ℂ) / (N : ℂ)) =
      (N : ℂ) ^ 2 * ∑' n : ℤ, 1 / ((b : ℂ) + (N : ℂ) * (n : ℂ)) ^ 2 := by
  simp only [inverseSquareRow, axis_term_scaling N hN b, tsum_mul_left]

/-- Actual ordinary summability of the one-dimensional inverse-square congruence series. -/
theorem axis_congruence_summable (N : ℕ) (hN : 0 < N) (b : ℤ) :
    Summable (fun n : ℤ => 1 / ((b : ℂ) + (N : ℂ) * (n : ℂ)) ^ 2) := by
  have hN0 : (N : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')
  have hs := (summable_shifted_row UpperHalfPlane.I ((b : ℂ) / (N : ℂ)) 0).div_const ((N : ℂ) ^ 2)
  apply hs.congr
  intro n
  simp only [Int.cast_zero, zero_mul, add_zero, axis_term_scaling N hN b]
  exact mul_div_cancel_left₀ _ hN0

/-- The one-dimensional series has the exact cyclotomic sum on each good axis class. -/
theorem axis_congruence_hasSum (N : ℕ) (hN : 0 < N) (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) :
    HasSum (fun n : ℤ => 1 / ((b : ℂ) + (N : ℂ) * (n : ℂ)) ^ 2)
      ((-4 * (Real.pi : ℂ) ^ 2 * Torsion.w N b / (1 - Torsion.w N b) ^ 2) / (N : ℂ) ^ 2) := by
  have hN0 : (N : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')
  apply (axis_congruence_summable N hN b).hasSum_iff.mpr
  apply (eq_div_iff hN0).mpr
  rw [mul_comm, ← inverseSquareRow_axis_scaling N hN b]
  exact inverseSquareRow_axis N hN b hb

/-- The actual weight-two axis constant is an absolutely convergent one-dimensional congruence sum. -/
theorem axisConstant_eq_congruence_row (N : ℕ) (hN : 0 < N) (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) :
    axisConstant N b = (N : ℂ) ^ 2 *
      (∑' n : ℤ, 1 / ((b : ℂ) + (N : ℂ) * (n : ℂ)) ^ 2) - (Real.pi : ℂ) ^ 2 / 3 := by
  rw [← inverseSquareRow_axis_scaling N hN b, inverseSquareRow_axis N hN b hb]
  rfl

#print axioms rowTail_summable_bound
#print axioms rowTail_tendsto
#print axioms inverseSquareRow_axis
#print axioms axisConstant_eq_congruence_row

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants
