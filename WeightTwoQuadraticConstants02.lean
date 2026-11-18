import WeightTwoProfiles02

/-!
# Actual quadratic constants and the Bernoulli profile

The actual completed weight-one value and its square are treated with their
unchanged zero convention. The quadratic definition of mu then yields a
Bernoulli-polynomial constant depending on the reduced first coordinate.
These are constants of actual functions and actual modular-form bundles.
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

/-- The all-label constant of the actual completed weight-one torsion value. -/
def lambdaConstant (N : ℕ) (a b : ℤ) : ℂ :=
  if (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b then 0 else
    TorsionWeierstrassData.scale *
      (if (N : ℤ) ∣ a then 1 / 2 + 1 / (Torsion.w N b - 1) else
        (firstRepresentative N a : ℂ) / (N : ℂ) - 1 / 2)

/-- The degree-two Bernoulli polynomial, in the exact complex normalization. -/
def bernoulliTwo (t : ℂ) : ℂ := t ^ 2 - t + 1 / 6

/-- The actual mu constant, extended by zero only at the bad torsion class. -/
def muConstant (N : ℕ) (a b : ℤ) : ℂ :=
  if (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b then 0 else
    -2 * (Real.pi : ℂ) ^ 2 * bernoulliTwo ((firstRepresentative N a : ℂ) / (N : ℂ))

lemma valueScale_sq : TorsionWeierstrassData.scale ^ 2 = -4 * (Real.pi : ℂ) ^ 2 := by
  norm_num [TorsionWeierstrassData.scale, mul_pow, Complex.I_sq]

lemma first_derivative_constants (N : ℕ) [NeZero N] (a : ℕ) (ha : a < N) (b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) :
    (Torsion.w N b)⁻¹ /
      (if a = 0 then 1 - (Torsion.w N b)⁻¹ else -(Torsion.w N b)⁻¹) =
      if a = 0 then 1 / (Torsion.w N b - 1) else -1 := by
  have hv := AllLevelTorsionCoefficients.w_ne_zero N b
  by_cases hz : a = 0
  · subst a
    have hb : ¬ (N : ℤ) ∣ b := by simpa using hg
    have hv1 : Torsion.w N b ≠ 1 := fun h => hb ((AllLevelTorsionCoefficients.w_eq_one_iff N b).mp h)
    have hd : Torsion.w N b - 1 ≠ 0 := sub_ne_zero.mpr hv1
    have hi : 1 - (Torsion.w N b)⁻¹ ≠ 0 := by
      intro h
      have he : (Torsion.w N b)⁻¹ = 1 := by linear_combination -h
      exact hv1 (by simpa using congrArg Inv.inv he)
    simp only [ite_true]
    field_simp [hv, hd, hi]
  · simp only [ite_eq_right hz]
    field_simp [hv]

lemma torsion_eq_scaled_theta (N : ℕ) [NeZero N] (a : ℕ) (ha : a < N) (b : ℤ) (τ : ℍ) :
    Torsion.torsionLogDerivative N a b τ = (a : ℂ) / (N : ℂ) + 1 / 2 +
      thetaOne N a b τ / thetaZero N a b τ := by
  rw [AllLevelPrincipalCoefficients.torsion_rep N a ha b τ,
    AllLevelPrincipalCoefficients.mSum_Q N a ha b τ,
    AllLevelPrincipalCoefficients.pSum_Q N a ha b τ]
  simp only [AllLevelPrincipalCoefficients.completion, thetaOne, thetaZero, thetaScale,
    ThetaG2.th_one, ThetaG2.th_zero]

/-- A closed normalized limit for the actual lambda value. -/
theorem lambdaValue_tendsto_normalized (N : ℕ) [NeZero N] (a : ℕ) (ha : a < N) (b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) :
    Tendsto (TorsionWeierstrassData.lambdaValue N a b) atImInfty
      (𝓝 (TorsionWeierstrassData.scale *
        (if a = 0 then 1 / 2 + 1 / (Torsion.w N b - 1) else (a : ℂ) / (N : ℂ) - 1 / 2))) := by
  have hp := thetaZero_tendsto N a ha b
  have hpn : (if a = 0 then 1 - (Torsion.w N b)⁻¹ else -(Torsion.w N b)⁻¹) ≠ 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      AllLevelPrincipalCoefficients.P_zero (NeZero.pos N) ha] using
      AllLevelPrincipalCoefficients.P_constant_ne_zero N a ha b hg
  have h := (((thetaOne_tendsto N a ha b).div hp hpn).const_add
    ((a : ℂ) / (N : ℂ) + 1 / 2)).const_mul TorsionWeierstrassData.scale
  simp only [Pi.div_apply] at h
  have he : (fun τ : ℍ => TorsionWeierstrassData.scale *
      ((a : ℂ) / (N : ℂ) + 1 / 2 + thetaOne N a b τ / thetaZero N a b τ)) =
      TorsionWeierstrassData.lambdaValue N a b := by
    funext τ
    rw [TorsionWeierstrassData.lambdaValue_of_good N a b τ hg,
      torsion_eq_scaled_theta N a ha b τ]
  rw [he, first_derivative_constants N a ha b hg] at h
  by_cases hz : a = 0
  · simpa only [ite_eq_left hz, hz, Nat.cast_zero, zero_div, zero_add, ite_true] using h
  · have hc : (a : ℂ) / (N : ℂ) + 1 / 2 + (-1 : ℂ) = (a : ℂ) / (N : ℂ) - 1 / 2 := by ring
    simpa only [ite_eq_right hz, hc] using h

lemma lambdaValue_bad (N : ℕ) (a b : ℤ) (hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) :
    TorsionWeierstrassData.lambdaValue N a b = fun _ : ℍ => (0 : ℂ) := by
  funext τ
  rw [TorsionWeierstrassData.lambdaValue, TorsionDistributionTwo.reg_of_bad hb, mul_zero]

lemma lambdaValue_representative (N : ℕ) (hN : 0 < N) (a b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    TorsionWeierstrassData.lambdaValue N a b =
      TorsionWeierstrassData.lambdaValue N (firstRepresentative N a) b := by
  have hg' : ¬ ((N : ℤ) ∣ (firstRepresentative N a : ℤ) ∧ (N : ℤ) ∣ b) := by
    rintro ⟨ha, hb⟩
    exact hg ⟨(firstRepresentative_dvd_iff N hN a).mp ha, hb⟩
  funext τ
  rw [TorsionWeierstrassData.lambdaValue_of_good N a b τ hg,
    TorsionWeierstrassData.lambdaValue_of_good N (firstRepresentative N a) b τ hg']
  congr 1
  have h := AllLevelForms.F_shift hN (a := (firstRepresentative N a : ℤ)) (b := b) hg'
    (a / (N : ℤ)) 0 τ
  simpa only [AllLevelForms.F, firstRepresentative_decomposition N hN a, mul_zero, add_zero] using h

/-- The actual lambda value tends to its exact constant for all integer labels. -/
theorem lambdaValue_tendsto (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    Tendsto (TorsionWeierstrassData.lambdaValue N a b) atImInfty (𝓝 (lambdaConstant N a b)) := by
  let : NeZero N := ⟨hN.ne'⟩
  by_cases hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · rw [lambdaValue_bad N a b hb, lambdaConstant, ite_eq_left hb]
    exact tendsto_const_nhds
  · have hg : ¬ ((N : ℤ) ∣ (firstRepresentative N a : ℤ) ∧ (N : ℤ) ∣ b) := by
      rintro ⟨ha, hb'⟩
      exact hb ⟨(firstRepresentative_dvd_iff N hN a).mp ha, hb'⟩
    have h := lambdaValue_tendsto_normalized N (firstRepresentative N a)
      (firstRepresentative_lt N hN a) b hg
    have hc : TorsionWeierstrassData.scale *
        (if firstRepresentative N a = 0 then 1 / 2 + 1 / (Torsion.w N b - 1) else
          (firstRepresentative N a : ℂ) / (N : ℂ) - 1 / 2) = lambdaConstant N a b := by
      simp only [lambdaConstant, ite_eq_right hb, firstRepresentative_zero_iff N hN a]
    rw [hc] at h
    rw [lambdaValue_representative N hN a b hb]
    exact h

/-- The exact quadratic constant relation, including every bad label. -/
theorem muConstant_relation (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    muConstant N a b = (lambdaConstant N a b ^ 2 - xConstant N a b) / 2 := by
  let : NeZero N := ⟨hN.ne'⟩
  by_cases hg : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · simp only [muConstant, lambdaConstant, xConstant, ite_eq_left hg, zero_pow (by norm_num : 2 ≠ 0),
      sub_self, zero_div]
  · by_cases ha : (N : ℤ) ∣ a
    · have hb : ¬ (N : ℤ) ∣ b := fun h => hg ⟨ha, h⟩
      have hv := AllLevelTorsionCoefficients.w_ne_zero N b
      have hv1 : Torsion.w N b ≠ 1 := fun h => hb ((AllLevelTorsionCoefficients.w_eq_one_iff N b).mp h)
      have hd : Torsion.w N b - 1 ≠ 0 := sub_ne_zero.mpr hv1
      have hd' : 1 - Torsion.w N b ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
      have hrep : firstRepresentative N a = 0 := (firstRepresentative_zero_iff N hN a).mpr ha
      simp only [muConstant, lambdaConstant, xConstant, ite_eq_right hg, ite_eq_left ha,
        hrep, Nat.cast_zero, zero_div, bernoulliTwo, axisConstant, mul_pow, valueScale_sq]
      field_simp [hv, hd, hd']
      ring
    · simp only [muConstant, lambdaConstant, xConstant, ite_eq_right hg, ite_eq_right ha,
        bernoulliTwo, mul_pow, valueScale_sq]
      ring

/-- The actual mu value has the closed Bernoulli constant, without a profile premise. -/
theorem muValue_tendsto (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    Tendsto (TorsionWeierstrassData.muValue N a b) atImInfty (𝓝 (muConstant N a b)) := by
  unfold TorsionWeierstrassData.muValue
  rw [muConstant_relation N hN a b]
  exact (((lambdaValue_tendsto N hN a b).pow 2).sub (xValue_tendsto N hN a b)).div_const 2

/-- Exact period-N constant of the actual lambda modular form. -/
theorem lambdaForm_coeff_zero (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    (qExpansion (N : ℝ) (WeierstrassForms.lambdaForm N hN a b)).coeff 0 = lambdaConstant N a b := by
  have h0 := ModularFormClass.tendsto_atImInfty (WeierstrassForms.lambdaForm N hN a b)
    (show (0 : ℝ) < N by exact_mod_cast hN) (principalPeriod_mem N)
  have he : (WeierstrassForms.lambdaForm N hN a b : ℍ → ℂ) = TorsionWeierstrassData.lambdaValue N a b :=
    funext (WeierstrassForms.lambdaForm_apply N hN a b)
  rw [he] at h0 ⊢
  exact tendsto_nhds_unique h0 (lambdaValue_tendsto N hN a b)

/-- Exact period-N constant of the actual mu modular form. -/
theorem muForm_coeff_zero (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    (qExpansion (N : ℝ) (WeierstrassForms.muForm N hN a b)).coeff 0 = muConstant N a b := by
  have h0 := ModularFormClass.tendsto_atImInfty (WeierstrassForms.muForm N hN a b)
    (show (0 : ℝ) < N by exact_mod_cast hN) (principalPeriod_mem N)
  have he : (WeierstrassForms.muForm N hN a b : ℍ → ℂ) = TorsionWeierstrassData.muValue N a b :=
    funext (WeierstrassForms.muForm_apply N hN a b)
  rw [he] at h0 ⊢
  exact tendsto_nhds_unique h0 (muValue_tendsto N hN a b)

/-- Exact period-N constant of the square of the actual completed torsion form. -/
theorem lambdaSquareForm_coeff_zero (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    (qExpansion (N : ℝ) (DivisionSeriesMembership.lambdaSquareForm N hN a b)).coeff 0 =
      lambdaConstant N a b ^ 2 := by
  have h0 := ModularFormClass.tendsto_atImInfty (DivisionSeriesMembership.lambdaSquareForm N hN a b)
    (show (0 : ℝ) < N by exact_mod_cast hN) (principalPeriod_mem N)
  have he : (DivisionSeriesMembership.lambdaSquareForm N hN a b : ℍ → ℂ) =
      fun τ : ℍ => TorsionWeierstrassData.lambdaValue N a b τ ^ 2 :=
    funext (DivisionSeriesMembership.lambdaSquareForm_apply N hN a b)
  rw [he] at h0 ⊢
  exact tendsto_nhds_unique h0 ((lambdaValue_tendsto N hN a b).pow 2)

#print axioms lambdaValue_tendsto
#print axioms muConstant_relation
#print axioms muValue_tendsto
#print axioms muForm_coeff_zero
#print axioms lambdaSquareForm_coeff_zero

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants
