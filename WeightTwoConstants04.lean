import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelDivisionSeriesMembership
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelPrincipalCoefficients
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionQuadraticGeneratorSpan
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Actual weight-two constants from the second theta moment

The second derivative is paired into the two convergent principal-period
branches. Its limit, together with the actual zeroth and first derivative
series, determines the constant of the unchanged Weierstrass torsion value.
No unregularized two-dimensional inverse-square sum is rearranged.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open Complex Filter
open UpperHalfPlane hiding I
open scoped Topology Real ModularForm MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants

open ZInQ.Contrib.HeckePrimeRationality
open AllLevelPrincipalCoefficients

/-- The derivative scale of the actual theta summands. -/
def thetaScale : ℂ := 2 * (Real.pi : ℂ) * Complex.I

lemma thetaScale_ne_zero : thetaScale ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

lemma thetaScale_sq : thetaScale ^ 2 = -4 * (Real.pi : ℂ) ^ 2 := by
  norm_num [thetaScale, mul_pow, Complex.I_sq]

/-- The genuine second-moment coefficients of both principal-period branches. -/
def secondSeries (N a : ℕ) (v : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (sparse (ep N a) (fun j => (j : ℂ) ^ 2 * cp v j)) +
    PowerSeries.mk (sparse (em N a) (fun j => (j + 1 : ℂ) ^ 2 * cm v j))

lemma sparse_ep_zero {N a : ℕ} (hN : 0 < N) (c : ℕ → ℂ) (hc : c 0 = 0) :
    sparse (ep N a) c 0 = 0 := by
  classical
  rw [sparse]
  split_ifs with h
  · have hj := le_ep (a := a) hN h.choose
    have hz : h.choose = 0 := by omega
    rw [hz, hc]
  · rfl

lemma firstSeries_zero {N a : ℕ} (hN : 0 < N) (ha : a < N) (v : ℂ) :
    (M N a v).coeff 0 = v⁻¹ := by
  have hem : em N a 0 = 0 := by simp [AllLevelPrincipalCoefficients.em, ThetaFiveTorsionCoefficients.tri]
  rw [M, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    sparse_ep_zero hN _ (by simp [dp]),
    sparse_zero _ (em_strict ha).injective hem]
  simp [dm]

lemma secondSeries_zero {N a : ℕ} (hN : 0 < N) (ha : a < N) (v : ℂ) :
    (secondSeries N a v).coeff 0 = -v⁻¹ := by
  have hem : em N a 0 = 0 := by simp [AllLevelPrincipalCoefficients.em, ThetaFiveTorsionCoefficients.tri]
  rw [secondSeries, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    sparse_ep_zero hN _ (by simp),
    sparse_zero _ (em_strict ha).injective hem]
  simp [cm]

/-- The scaled actual zeroth theta derivative. -/
def thetaZero (N a : ℕ) (b : ℤ) (τ : ℍ) : ℂ :=
  Q N τ ^ a * ThetaG2.th 0 (Torsion.shiftedPoint N a b τ) τ

/-- The scaled actual first theta derivative. -/
def thetaOne (N a : ℕ) (b : ℤ) (τ : ℍ) : ℂ :=
  Q N τ ^ a * (ThetaG2.th 1 (Torsion.shiftedPoint N a b τ) τ / thetaScale)

/-- The scaled actual second theta derivative. -/
def thetaTwo (N a : ℕ) (b : ℤ) (τ : ℍ) : ℂ :=
  Q N τ ^ a * (ThetaG2.th 2 (Torsion.shiftedPoint N a b τ) τ / thetaScale ^ 2)

lemma summable_th (k : ℕ) (τ : ℍ) (z : ℂ) :
    Summable (fun n : ℤ => (2 * (Real.pi : ℂ) * I * n) ^ k * jacobiTheta₂_term n z τ) := by
  exact Summable.of_norm_bounded
    ((summable_pow_mul_jacobiTheta₂_term_bound |z.im| τ.im_pos k).mul_left ((2 * Real.pi) ^ k))
    (fun n => ThetaG2.norm_term_coeff_le k τ.im_pos le_rfl le_rfl n)

/-- Ordinary convergence of the second derivative's paired series, at every upper-half-plane point. -/
theorem secondSeries_hasSum (N : ℕ) [NeZero N] (a : ℕ) (ha : a < N) (b : ℤ) (τ : ℍ) :
    HasSum (fun m => (secondSeries N a (Torsion.w N b)).coeff m * Q N τ ^ m)
      (thetaTwo N a b τ) := by
  have hg0 := ((summable_th 2 τ (Torsion.shiftedPoint N a b τ)).hasSum.div_const
    (thetaScale ^ 2)).mul_left (Q N τ ^ a)
  have hg : HasSum (fun n : ℤ => Q N τ ^ a *
      ((n : ℂ) ^ 2 * jacobiTheta₂_term n (Torsion.shiftedPoint N a b τ) τ))
      (thetaTwo N a b τ) := by
    apply hg0.congr_fun
    intro n
    rw [show 2 * (Real.pi : ℂ) * I * n = thetaScale * n by rfl, mul_pow]
    field_simp [thetaScale_ne_zero]
  have hp (j : ℕ) : Q N τ ^ a * ((j : ℂ) ^ 2 *
      jacobiTheta₂_term j (Torsion.shiftedPoint N a b τ) τ) =
      ((j : ℂ) ^ 2 * cp (Torsion.w N b) j) * Q N τ ^ ep N a j := by
    rw [mul_left_comm, theta_positive N a b τ]
    ring
  have hm (j : ℕ) : Q N τ ^ a * (((-((j : ℤ) + 1) : ℤ) : ℂ) ^ 2 *
      jacobiTheta₂_term (-((j : ℤ) + 1)) (Torsion.shiftedPoint N a b τ) τ) =
      ((j + 1 : ℂ) ^ 2 * cm (Torsion.w N b) j) * Q N τ ^ em N a j := by
    rw [mul_left_comm, theta_negative N a ha b τ]
    push_cast
    ring
  simpa only [secondSeries, map_add, PowerSeries.coeff_mk] using
    paired_sparse_hasSum (ep N a) (em N a) (ep_strict (NeZero.pos N)).injective
      (em_strict ha).injective
      (fun j => (j : ℂ) ^ 2 * cp (Torsion.w N b) j)
      (fun j => (j + 1 : ℂ) ^ 2 * cm (Torsion.w N b) j) (Q N τ)
      (fun n => Q N τ ^ a * ((n : ℂ) ^ 2 *
        jacobiTheta₂_term n (Torsion.shiftedPoint N a b τ) τ)) hg
      (by intro j; simpa only [Int.cast_natCast] using hp j) hm

/-- The zeroth derivative's limit keeps both branches when the first coordinate is zero. -/
theorem thetaZero_tendsto (N : ℕ) [NeZero N] (a : ℕ) (ha : a < N) (b : ℤ) :
    Tendsto (thetaZero N a b) atImInfty
      (𝓝 (if a = 0 then 1 - (Torsion.w N b)⁻¹ else -(Torsion.w N b)⁻¹)) := by
  have h := tendsto_atImInfty_of_hasSum_qExpansion (h := (N : ℝ))
    (by exact_mod_cast NeZero.pos N) (fun τ => by
      simpa only [smul_eq_mul, Q] using P_hasSum N a ha b τ)
  unfold thetaZero
  simp_rw [ThetaG2.th_zero]
  simpa only [Q, P_zero (NeZero.pos N) ha] using h

/-- The first derivative's actual constant. -/
theorem thetaOne_tendsto (N : ℕ) [NeZero N] (a : ℕ) (ha : a < N) (b : ℤ) :
    Tendsto (thetaOne N a b) atImInfty (𝓝 ((Torsion.w N b)⁻¹)) := by
  have h := tendsto_atImInfty_of_hasSum_qExpansion (h := (N : ℝ))
    (by exact_mod_cast NeZero.pos N) (fun τ => by
      simpa only [smul_eq_mul, Q] using M_hasSum N a ha b τ)
  unfold thetaOne
  simp_rw [ThetaG2.th_one]
  simpa only [Q, thetaScale, firstSeries_zero (NeZero.pos N) ha] using h

/-- The second derivative's actual constant, proved from its convergent series. -/
theorem thetaTwo_tendsto (N : ℕ) [NeZero N] (a : ℕ) (ha : a < N) (b : ℤ) :
    Tendsto (thetaTwo N a b) atImInfty (𝓝 (-(Torsion.w N b)⁻¹)) := by
  have h := tendsto_atImInfty_of_hasSum_qExpansion (h := (N : ℝ))
    (by exact_mod_cast NeZero.pos N) (fun τ => by
      simpa only [smul_eq_mul, Q] using secondSeries_hasSum N a ha b τ)
  simpa only [secondSeries_zero (NeZero.pos N) ha] using h

/-- The symmetric-row G2 has the classical constant, not the invariant g2 of weight four. -/
theorem G2_tendsto : Tendsto EisensteinSeries.G2 atImInfty (𝓝 ((Real.pi : ℂ) ^ 2 / 3)) := by
  have hc : 2 * riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 3 := by
    rw [riemannZeta_two]
    ring
  rw [ThetaG2.G2_eq_smul_E2]
  change Tendsto (fun τ : ℍ => (2 * riemannZeta 2) * EisensteinSeries.E2 τ) atImInfty _
  simpa only [mul_one, hc] using
    EisensteinSeries.tendsto_E2_atImInfty.const_mul (2 * riemannZeta 2)

/-- Identification of the actual x-value with the scaled derivative quotients. -/
theorem xValue_eq_scaled_theta (N : ℕ) [NeZero N] (a : ℕ) (b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) :
    TorsionWeierstrassData.xValue N a b τ = thetaScale ^ 2 *
      ((thetaOne N a b τ / thetaZero N a b τ) ^ 2 - thetaTwo N a b τ / thetaZero N a b τ) -
      EisensteinSeries.G2 τ := by
  have hθ : ThetaG2.th 0 (Torsion.shiftedPoint N a b τ) τ ≠ 0 := by
    rw [ThetaG2.th_zero]
    exact AllLevelTheta.jacobiTheta₂_shiftedPoint_ne_zero N (NeZero.pos N) τ a b hg
  have hQ : Q N τ ^ a ≠ 0 := pow_ne_zero _ (Q_ne_zero N τ)
  rw [WeierstrassForms.xValue_eq_th (NeZero.pos N) a b τ hg,
    ThetaG2.finitePart_eq_neg_G2]
  unfold thetaOne thetaZero thetaTwo
  field_simp [hθ, hQ, thetaScale_ne_zero]
  ring

/-- The exact cyclotomic quotient algebra for the constants of the three derivatives. -/
lemma derivative_constants {N a : ℕ} [NeZero N] (ha : a < N) (b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) :
    (((Torsion.w N b)⁻¹ / (if a = 0 then 1 - (Torsion.w N b)⁻¹ else -(Torsion.w N b)⁻¹)) ^ 2 -
      (-(Torsion.w N b)⁻¹ / (if a = 0 then 1 - (Torsion.w N b)⁻¹ else -(Torsion.w N b)⁻¹))) =
      if a = 0 then Torsion.w N b / (1 - Torsion.w N b) ^ 2 else 0 := by
  have hv := AllLevelTorsionCoefficients.w_ne_zero N b
  by_cases hz : a = 0
  · subst a
    have hb : ¬ (N : ℤ) ∣ b := by simpa using hg
    have hv1 : Torsion.w N b ≠ 1 := fun h => hb ((AllLevelTorsionCoefficients.w_eq_one_iff N b).mp h)
    have hd : 1 - Torsion.w N b ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
    have hi : 1 - (Torsion.w N b)⁻¹ ≠ 0 := by
      intro h
      have he : (Torsion.w N b)⁻¹ = 1 := by linear_combination -h
      exact hv1 (by simpa using congrArg Inv.inv he)
    simp only [ite_true]
    field_simp [hv, hd, hi]
    ring
  · simp only [ite_eq_right hz]
    field_simp [hv]
    ring

/-- The full normalized-row constant of the unchanged actual weight-two torsion value. -/
theorem xValue_tendsto_normalized (N : ℕ) [NeZero N] (a : ℕ) (ha : a < N) (b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) :
    Tendsto (TorsionWeierstrassData.xValue N a b) atImInfty
      (𝓝 (if a = 0 then -4 * (Real.pi : ℂ) ^ 2 * Torsion.w N b /
        (1 - Torsion.w N b) ^ 2 - (Real.pi : ℂ) ^ 2 / 3 else -(Real.pi : ℂ) ^ 2 / 3)) := by
  have hp := thetaZero_tendsto N a ha b
  have hpn : (if a = 0 then 1 - (Torsion.w N b)⁻¹ else -(Torsion.w N b)⁻¹) ≠ 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      P_zero (NeZero.pos N) ha] using P_constant_ne_zero N a ha b hg
  have h := ((((thetaOne_tendsto N a ha b).div hp hpn).pow 2).sub
    ((thetaTwo_tendsto N a ha b).div hp hpn)).const_mul (thetaScale ^ 2) |>.sub G2_tendsto
  have he : (fun τ : ℍ => thetaScale ^ 2 *
      ((thetaOne N a b τ / thetaZero N a b τ) ^ 2 - thetaTwo N a b τ / thetaZero N a b τ) -
      EisensteinSeries.G2 τ) = TorsionWeierstrassData.xValue N a b :=
    funext (fun τ => (xValue_eq_scaled_theta N a b τ hg).symm)
  simp only [Pi.div_apply] at h
  rw [he, derivative_constants ha b hg, thetaScale_sq] at h
  by_cases hz : a = 0
  · simpa only [ite_eq_left hz, mul_div_assoc] using h
  · simpa only [ite_eq_right hz, mul_zero, zero_sub, neg_div] using h

#print axioms secondSeries_hasSum
#print axioms thetaTwo_tendsto
#print axioms xValue_eq_scaled_theta
#print axioms xValue_tendsto_normalized

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants
