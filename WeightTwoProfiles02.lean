import WeightTwoConstants04

/-!
# Exact actual division-form constants at every integral slash representative

The first coordinate is reduced to its principal-period representative. The
zero torsion class retains its stipulated zero value. Every displayed
constant is the zeroth coefficient of the actual period-N expansion of the
unchanged convergent division Eisenstein modular form.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open Complex Filter Matrix ModularForm
open UpperHalfPlane hiding I
open scoped Topology Real ModularForm MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants

open ZInQ.Contrib.HeckePrimeRationality

/-- The classical cyclotomic axis term of the actual Weierstrass value. -/
def axisConstant (N : ℕ) (b : ℤ) : ℂ :=
  -4 * (Real.pi : ℂ) ^ 2 * Torsion.w N b / (1 - Torsion.w N b) ^ 2 -
    (Real.pi : ℂ) ^ 2 / 3

/-- The all-label constant, including the independently stipulated bad-label zero. -/
def xConstant (N : ℕ) (a b : ℤ) : ℂ :=
  if (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b then 0 else
    if (N : ℤ) ∣ a then axisConstant N b else -(Real.pi : ℂ) ^ 2 / 3

/-- The principal-period first-coordinate representative. -/
def firstRepresentative (N : ℕ) (a : ℤ) : ℕ := (a % (N : ℤ)).toNat

lemma firstRepresentative_cast (N : ℕ) (hN : 0 < N) (a : ℤ) :
    (firstRepresentative N a : ℤ) = a % (N : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg a (by exact_mod_cast hN.ne'))

lemma firstRepresentative_lt (N : ℕ) (hN : 0 < N) (a : ℤ) :
    firstRepresentative N a < N := by
  have hc := firstRepresentative_cast N hN a
  have hr := Int.emod_lt_of_pos a (show (0 : ℤ) < N by exact_mod_cast hN)
  omega

lemma firstRepresentative_decomposition (N : ℕ) (hN : 0 < N) (a : ℤ) :
    (firstRepresentative N a : ℤ) + (N : ℤ) * (a / (N : ℤ)) = a := by
  rw [firstRepresentative_cast N hN a]
  have h := Int.mul_ediv_add_emod a (N : ℤ)
  omega

lemma firstRepresentative_dvd_iff (N : ℕ) (hN : 0 < N) (a : ℤ) :
    (N : ℤ) ∣ (firstRepresentative N a : ℤ) ↔ (N : ℤ) ∣ a := by
  nth_rw 2 [← firstRepresentative_decomposition N hN a]
  exact (dvd_add_left (dvd_mul_right (N : ℤ) (a / (N : ℤ)))).symm

lemma firstRepresentative_zero_iff (N : ℕ) (hN : 0 < N) (a : ℤ) :
    firstRepresentative N a = 0 ↔ (N : ℤ) ∣ a := by
  constructor
  · intro h
    apply (firstRepresentative_dvd_iff N hN a).mp
    simp [h]
  · intro h
    apply Nat.eq_zero_of_dvd_of_lt _ (firstRepresentative_lt N hN a)
    exact_mod_cast (firstRepresentative_dvd_iff N hN a).mpr h

lemma xValue_representative (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    TorsionWeierstrassData.xValue N a b =
      TorsionWeierstrassData.xValue N (firstRepresentative N a) b := by
  funext τ
  have h := WeierstrassDistributionNat.xValue_shift hN (firstRepresentative N a) b
    (a / (N : ℤ)) 0 τ
  simpa only [firstRepresentative_decomposition N hN a, mul_zero, add_zero] using h

/-- The exact limit of the actual x-value for all signed integral labels and every positive level. -/
theorem xValue_tendsto (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    Tendsto (TorsionWeierstrassData.xValue N a b) atImInfty (𝓝 (xConstant N a b)) := by
  let : NeZero N := ⟨hN.ne'⟩
  by_cases hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · have he : TorsionWeierstrassData.xValue N a b = fun _ : ℍ => (0 : ℂ) :=
      funext (WeierstrassForms.xValue_bad hb)
    rw [he, xConstant, ite_eq_left hb]
    exact tendsto_const_nhds
  · have hg : ¬ ((N : ℤ) ∣ (firstRepresentative N a : ℤ) ∧ (N : ℤ) ∣ b) := by
      rintro ⟨ha, hb'⟩
      exact hb ⟨(firstRepresentative_dvd_iff N hN a).mp ha, hb'⟩
    have h := xValue_tendsto_normalized N (firstRepresentative N a)
      (firstRepresentative_lt N hN a) b hg
    have hc : (if firstRepresentative N a = 0 then
        -4 * (Real.pi : ℂ) ^ 2 * Torsion.w N b / (1 - Torsion.w N b) ^ 2 -
          (Real.pi : ℂ) ^ 2 / 3 else -(Real.pi : ℂ) ^ 2 / 3) = xConstant N a b := by
      simp only [xConstant, ite_eq_right hb, axisConstant, firstRepresentative_zero_iff N hN a]
    rw [hc] at h
    rw [xValue_representative N hN a b]
    exact h

/-- The exact positive principal period used for all constants. -/
lemma principalPeriod_mem (N : ℕ) :
    (N : ℝ) ∈ ((CongruenceSubgroup.Gamma N).map (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩

/-- The zeroth coefficient of the actual independently defined division Eisenstein form. -/
theorem divisionEisensteinMF_coeff_zero (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    (qExpansion (N : ℝ) (EisensteinWeightTwo.divisionEisensteinMF N hN ![a, b])).coeff 0 =
      xConstant N a b := by
  have h0 := ModularFormClass.tendsto_atImInfty
    (EisensteinWeightTwo.divisionEisensteinMF N hN ![a, b])
    (show (0 : ℝ) < N by exact_mod_cast hN) (principalPeriod_mem N)
  have he : (EisensteinWeightTwo.divisionEisensteinMF N hN ![a, b] : ℍ → ℂ) =
      TorsionWeierstrassData.xValue N a b :=
    funext (EisensteinWeightTwo.divisionEisensteinMF_eq_xValue_all N hN a b)
  rw [he] at h0 ⊢
  exact tendsto_nhds_unique h0 (xValue_tendsto N hN a b)

/-- The zeroth coefficient of the actual Weierstrass modular form agrees with the same series constant. -/
theorem xForm_coeff_zero (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    (qExpansion (N : ℝ) (WeierstrassForms.xForm N hN a b)).coeff 0 = xConstant N a b := by
  rw [DivisionSeriesMembership.xForm_eq_divisionEisensteinMF]
  exact divisionEisensteinMF_coeff_zero N hN a b

/-- Exact constant profile at every integral slash representative, with the actual right label action. -/
theorem divisionEisensteinMF_slash_coeff_zero (N : ℕ) (hN : 0 < N)
    (a : Fin 2 → ℤ) (γ : SL(2, ℤ)) :
    (qExpansion (N : ℝ)
      ((EisensteinWeightTwo.divisionEisensteinMF N hN a : ℍ → ℂ) ∣[(2 : ℤ)] γ)).coeff 0 =
      xConstant N ((a ᵥ* γ.1) 0) ((a ᵥ* γ.1) 1) := by
  change (qExpansion (N : ℝ)
    ((fun τ : ℍ => EisensteinWeightTwo.divisionEisenstein N (a 0) (a 1) τ) ∣[(2 : ℤ)] γ)).coeff 0 = _
  rw [EisensteinWeightTwo.divisionEisenstein_slash N hN a γ]
  exact divisionEisensteinMF_coeff_zero N hN ((a ᵥ* γ.1) 0) ((a ᵥ* γ.1) 1)

/-- The actual x-form and the independent lattice series have the same full slash profile. -/
theorem xForm_slash_coeff_zero (N : ℕ) (hN : 0 < N) (a b : ℤ) (γ : SL(2, ℤ)) :
    (qExpansion (N : ℝ) ((WeierstrassForms.xForm N hN a b : ℍ → ℂ) ∣[(2 : ℤ)] γ)).coeff 0 =
      xConstant N ((![a, b] ᵥ* γ.1) 0) ((![a, b] ᵥ* γ.1) 1) := by
  rw [DivisionSeriesMembership.xForm_eq_divisionEisensteinMF]
  exact divisionEisensteinMF_slash_coeff_zero N hN ![a, b] γ

/-- The actual zero class has zero constant; it is not assigned a pole value. -/
theorem xConstant_bad (N : ℕ) (a b : ℤ) (hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) :
    xConstant N a b = 0 := by
  simp only [xConstant, ite_eq_left hb]

/-- Every non-axis congruence row has the same genuine finite-part constant. -/
theorem xConstant_nonaxis (N : ℕ) (a b : ℤ) (ha : ¬ (N : ℤ) ∣ a) :
    xConstant N a b = -(Real.pi : ℂ) ^ 2 / 3 := by
  have hb : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) := fun h => ha h.1
  simp only [xConstant, ite_eq_right hb, ite_eq_right ha]

/-- Every good axis row has the exact cyclotomic constant. -/
theorem xConstant_axis (N : ℕ) (a b : ℤ) (ha : (N : ℤ) ∣ a) (hb : ¬ (N : ℤ) ∣ b) :
    xConstant N a b = axisConstant N b := by
  have hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) := fun h => hb h.2
  simp only [xConstant, ite_eq_right hg, ite_eq_left ha]

#print axioms xValue_tendsto
#print axioms divisionEisensteinMF_coeff_zero
#print axioms divisionEisensteinMF_slash_coeff_zero
#print axioms xForm_slash_coeff_zero

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants
