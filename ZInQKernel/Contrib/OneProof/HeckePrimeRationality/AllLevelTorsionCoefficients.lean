import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionDefinitions
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveTorsionCoefficients
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Coefficient arithmetic of torsion theta functions at every positive level

The triangular formal series are independent of the level. Their actual
scalar sums give the theta denominator and scaled derivative. Local
nonvanishing at the cusp suffices for the quotient expansion; no global
theta nonvanishing or modular-form spanning theorem is assumed.
-/

noncomputable section

open Complex UpperHalfPlane Filter
open scoped Topology

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients

open ZInQ.Contrib.HeckePrimeRationality.Torsion
open ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsionCoefficients
  (tri two_mul_tri tri_injective le_tri pPair mPair triangularCoeff triangularCoeff_not_range
   P M R P_coeff_tri M_coeff_tri P_coeff_zero M_coeff_zero q cuspFunction_eventually_eq
   map_P map_M map_R)

variable (N : ℕ) [NeZero N]

lemma w_eq_exp (b : ℤ) :
    w N b = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * b / (N : ℂ)) := by
  rw [w, zeta, ← Complex.exp_int_mul]
  congr 1
  ring

lemma w_ne_zero (b : ℤ) : w N b ≠ 0 := by
  rw [w_eq_exp]
  exact Complex.exp_ne_zero _

lemma norm_w (b : ℤ) : ‖w N b‖ = 1 := by
  rw [w_eq_exp, Complex.norm_exp]
  simp

lemma theta_term_nat (b : ℤ) (τ : ℍ) (j : ℕ) :
    jacobiTheta₂_term j (shiftedPoint N 0 b τ) τ =
      (-1 : ℂ) ^ j * w N b ^ j * q τ ^ tri j := by
  have htri : (2 : ℂ) * (tri j : ℂ) = (j : ℂ) * ((j : ℂ) + 1) := by
    exact_mod_cast two_mul_tri j
  have he : 2 * (Real.pi : ℂ) * Complex.I * j * shiftedPoint N 0 b τ +
      (Real.pi : ℂ) * Complex.I * (j : ℂ) ^ 2 * (τ : ℂ) =
      (j : ℂ) * ((Real.pi : ℂ) * Complex.I) +
      (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * b / (N : ℂ)) +
      (tri j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * τ) := by
    dsimp [shiftedPoint]
    linear_combination -(Real.pi : ℂ) * Complex.I * (τ : ℂ) * htri
  rw [jacobiTheta₂_term]
  push_cast
  rw [he, Complex.exp_add, Complex.exp_add,
    Complex.exp_nat_mul, Complex.exp_nat_mul, Complex.exp_nat_mul,
    Complex.exp_pi_mul_I, ← w_eq_exp]
  simp [q, Function.Periodic.qParam]

lemma theta_term_neg (b : ℤ) (τ : ℍ) (j : ℕ) :
    jacobiTheta₂_term (-((j : ℤ) + 1)) (shiftedPoint N 0 b τ) τ =
      -(-1 : ℂ) ^ j * (w N b ^ (j + 1))⁻¹ * q τ ^ tri j := by
  have htri : (2 : ℂ) * (tri j : ℂ) = (j : ℂ) * ((j : ℂ) + 1) := by
    exact_mod_cast two_mul_tri j
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((-((j : ℤ) + 1) : ℤ) : ℂ) * shiftedPoint N 0 b τ +
      (Real.pi : ℂ) * Complex.I * (((-((j : ℤ) + 1) : ℤ) : ℂ)) ^ 2 * (τ : ℂ) =
      -((j + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) +
      -((j + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * b / (N : ℂ)) +
      (tri j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * τ) := by
    dsimp [shiftedPoint]
    push_cast
    linear_combination -(Real.pi : ℂ) * Complex.I * (τ : ℂ) * htri
  rw [jacobiTheta₂_term, he, Complex.exp_add, Complex.exp_add,
    neg_mul, neg_mul, Complex.exp_neg, Complex.exp_neg,
    Complex.exp_nat_mul, Complex.exp_nat_mul, Complex.exp_nat_mul,
    Complex.exp_pi_mul_I, ← w_eq_exp]
  simp [q, Function.Periodic.qParam, pow_succ]
  left
  rw [← inv_pow]
  norm_num

lemma theta_pair (b : ℤ) (τ : ℍ) (j : ℕ) :
    jacobiTheta₂_term j (shiftedPoint N 0 b τ) τ +
      jacobiTheta₂_term (-((j : ℤ) + 1)) (shiftedPoint N 0 b τ) τ =
      pPair (w N b) j * q τ ^ tri j := by
  rw [theta_term_nat, theta_term_neg]
  dsimp [pPair]
  ring

lemma derivative_pair (b : ℤ) (τ : ℍ) (j : ℕ) :
    (j : ℂ) * jacobiTheta₂_term j (shiftedPoint N 0 b τ) τ +
      ((-((j : ℤ) + 1) : ℤ) : ℂ) *
        jacobiTheta₂_term (-((j : ℤ) + 1)) (shiftedPoint N 0 b τ) τ =
      mPair (w N b) j * q τ ^ tri j := by
  rw [theta_term_nat, theta_term_neg]
  dsimp [mPair]
  push_cast
  ring

lemma P_hasSum (b : ℤ) (τ : ℍ) :
    HasSum (fun m : ℕ => (P (w N b)).coeff m * q τ ^ m)
      (jacobiTheta₂ (shiftedPoint N 0 b τ) τ) := by
  have hp := (hasSum_jacobiTheta₂_term (shiftedPoint N 0 b τ) τ.im_pos).nat_add_neg_add_one
  have hp' : HasSum (fun j : ℕ => pPair (w N b) j * q τ ^ tri j)
      (jacobiTheta₂ (shiftedPoint N 0 b τ) τ) := by
    simpa only [theta_pair] using hp
  apply (tri_injective.hasSum_iff (f := fun m : ℕ => (P (w N b)).coeff m * q τ ^ m) ?_).mp
  · change HasSum (fun j : ℕ => (P (w N b)).coeff (tri j) * q τ ^ tri j) _
    simpa only [P_coeff_tri] using hp'
  · intro m hm
    simp [P, triangularCoeff_not_range _ _ hm]

lemma M_hasSum (b : ℤ) (τ : ℍ) :
    HasSum (fun m : ℕ => (M (w N b)).coeff m * q τ ^ m)
      (jacobiTheta₂' (shiftedPoint N 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I)) := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hscaled : HasSum (fun n : ℤ => (n : ℂ) * jacobiTheta₂_term n (shiftedPoint N 0 b τ) τ)
      (jacobiTheta₂' (shiftedPoint N 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I)) := by
    convert (hasSum_jacobiTheta₂'_term (shiftedPoint N 0 b τ) τ.im_pos).div_const
      (2 * (Real.pi : ℂ) * Complex.I) using 1
    ext n
    dsimp [jacobiTheta₂'_term]
    field_simp
  have hm := hscaled.nat_add_neg_add_one
  have hm' : HasSum (fun j : ℕ => mPair (w N b) j * q τ ^ tri j)
      (jacobiTheta₂' (shiftedPoint N 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I)) := by
    simpa only [Int.cast_natCast, derivative_pair] using hm
  apply (tri_injective.hasSum_iff (f := fun m : ℕ => (M (w N b)).coeff m * q τ ^ m) ?_).mp
  · change HasSum (fun j : ℕ => (M (w N b)).coeff (tri j) * q τ ^ tri j) _
    simpa only [M_coeff_tri] using hm'
  · intro m hm
    simp [M, triangularCoeff_not_range _ _ hm]

lemma P_coeff_norm_le_two (b : ℤ) (m : ℕ) : ‖(P (w N b)).coeff m‖ ≤ 2 := by
  classical
  rw [P, PowerSeries.coeff_mk, triangularCoeff]
  split_ifs with h
  · dsimp [pPair]
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc
      ‖w N b ^ h.choose - (w N b ^ (h.choose + 1))⁻¹‖ ≤
          ‖w N b ^ h.choose‖ + ‖(w N b ^ (h.choose + 1))⁻¹‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, norm_w, norm_inv]
  · simp

lemma M_coeff_norm_le (b : ℤ) (m : ℕ) : ‖(M (w N b)).coeff m‖ ≤ 2 * m + 1 := by
  classical
  rw [M, PowerSeries.coeff_mk, triangularCoeff]
  split_ifs with h
  · have hj : h.choose ≤ m := (le_tri h.choose).trans_eq h.choose_spec
    dsimp [mPair]
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc
      ‖(h.choose : ℂ) * w N b ^ h.choose +
          (h.choose + 1 : ℂ) * (w N b ^ (h.choose + 1))⁻¹‖ ≤
          ‖(h.choose : ℂ) * w N b ^ h.choose‖ +
          ‖(h.choose + 1 : ℂ) * (w N b ^ (h.choose + 1))⁻¹‖ := norm_add_le _ _
      _ = (h.choose : ℝ) + (h.choose + 1) := by
        simp only [norm_mul, norm_pow, norm_w, norm_inv, one_pow, inv_one,
          mul_one, Complex.norm_natCast]
        have hcast : (h.choose : ℂ) + 1 = ((h.choose + 1 : ℕ) : ℂ) := by push_cast; rfl
        rw [hcast, Complex.norm_natCast]
        norm_cast
      _ ≤ 2 * m + 1 := by exact_mod_cast (show h.choose + (h.choose + 1) ≤ 2 * m + 1 by omega)
  · simp only [norm_zero]
    positivity

lemma P_radius (b : ℤ) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ (fun m => (P (w N b)).coeff m)).radius := by
  apply FormalMultilinearSeries.le_radius_of_bound _ 2 (r := 1)
  intro m
  simpa only [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow, mul_one]
    using P_coeff_norm_le_two N b m

lemma M_radius (b : ℤ) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ (fun m => (M (w N b)).coeff m)).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have hr' : (r : ℝ) < 1 := by exact_mod_cast hr
  have hs0 := summable_geometric_of_lt_one r.2 hr'
  have hs1 : Summable (fun m : ℕ => (m : ℝ) * (r : ℝ) ^ m) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := (r : ℝ)) (by
        change ‖(r : ℝ)‖ < 1
        rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ (r : ℝ) by positivity)]
        exact hr')
  have hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * (r : ℝ) ^ m) := by
    simpa [add_mul, mul_assoc] using (hs1.mul_left 2).add hs0
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  simp only [FormalMultilinearSeries.ofScalars_norm]
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun m => mul_le_mul_of_nonneg_right (M_coeff_norm_le N b m) (by positivity)) hs

def pSum (b : ℤ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (fun m => (P (w N b)).coeff m)

def mSum (b : ℤ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (fun m => (M (w N b)).coeff m)

lemma pSum_analytic (b : ℤ) : AnalyticAt ℂ (pSum N b) 0 :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall _ (zero_lt_one.trans_le (P_radius N b))).analyticAt

lemma mSum_analytic (b : ℤ) : AnalyticAt ℂ (mSum N b) 0 :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall _ (zero_lt_one.trans_le (M_radius N b))).analyticAt

lemma pSum_q (b : ℤ) (τ : ℍ) :
    pSum N b (q τ) = jacobiTheta₂ (shiftedPoint N 0 b τ) τ := by
  rw [pSum, FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul] using (P_hasSum N b τ).tsum_eq

lemma mSum_q (b : ℤ) (τ : ℍ) :
    mSum N b (q τ) = jacobiTheta₂' (shiftedPoint N 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [mSum, FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul] using (M_hasSum N b τ).tsum_eq

lemma pSum_zero (b : ℤ) : pSum N b 0 = 1 - (w N b)⁻¹ := by
  simp [pSum, FormalMultilinearSeries.ofScalarsSum_zero, P_coeff_zero]

lemma mSum_zero (b : ℤ) : mSum N b 0 = (w N b)⁻¹ := by
  simp [mSum, FormalMultilinearSeries.ofScalarsSum_zero, M_coeff_zero]

lemma p_cusp_analytic (b : ℤ) :
    AnalyticAt ℂ (cuspFunction 1 (fun τ : ℍ => jacobiTheta₂ (shiftedPoint N 0 b τ) τ)) 0 :=
  (pSum_analytic N b).congr (cuspFunction_eventually_eq (fun τ => (pSum_q N b τ).symm)
    (pSum_analytic N b).continuousAt).symm

lemma m_cusp_analytic (b : ℤ) :
    AnalyticAt ℂ (cuspFunction 1 (fun τ : ℍ =>
      jacobiTheta₂' (shiftedPoint N 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I))) 0 :=
  (mSum_analytic N b).congr (cuspFunction_eventually_eq (fun τ => (mSum_q N b τ).symm)
    (mSum_analytic N b).continuousAt).symm

lemma P_qExpansion (b : ℤ) :
    qExpansion 1 (fun τ : ℍ => jacobiTheta₂ (shiftedPoint N 0 b τ) τ) = P (w N b) := by
  ext m
  symm
  exact TauCeti.UpperHalfPlane.qExpansion_coeff_unique
    (c := fun n => (P (w N b)).coeff n) one_pos (p_cusp_analytic N b)
    (fun τ => by simpa only [q, smul_eq_mul] using P_hasSum N b τ) m

lemma M_qExpansion (b : ℤ) :
    qExpansion 1 (fun τ : ℍ =>
      jacobiTheta₂' (shiftedPoint N 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I)) = M (w N b) := by
  ext m
  symm
  exact TauCeti.UpperHalfPlane.qExpansion_coeff_unique
    (c := fun n => (M (w N b)).coeff n) one_pos (m_cusp_analytic N b)
    (fun τ => by simpa only [q, smul_eq_mul] using M_hasSum N b τ) m

lemma w_eq_one_iff (b : ℤ) : w N b = 1 ↔ (N : ℤ) ∣ b := by
  let u : ℂˣ := Units.mk0 (zeta N) (Complex.exp_ne_zero _)
  have hprim : IsPrimitiveRoot u N := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    exact Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have h := hprim.zpow_eq_one_iff_dvd b
  constructor
  · intro hb
    apply h.mp
    apply Units.ext
    simp only [Units.val_zpow_eq_zpow_val, Units.val_one]
    change zeta N ^ b = 1
    exact hb
  · intro hb
    have h' := congrArg Units.val (h.mpr hb)
    simp only [Units.val_zpow_eq_zpow_val, Units.val_one] at h'
    change zeta N ^ b = 1 at h'
    exact h'

lemma P_constant_ne_zero (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) :
    PowerSeries.constantCoeff (P (w N b)) ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, P_coeff_zero]
  intro h
  have hi : (w N b)⁻¹ = 1 := by linear_combination -h
  have hw : w N b = 1 := by simpa using congrArg Inv.inv hi
  exact hb ((w_eq_one_iff N b).mp hw)

lemma pSum_zero_ne (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) : pSum N b 0 ≠ 0 := by
  simpa only [pSum_zero, ← P_coeff_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    using P_constant_ne_zero N b hb

/-- This representation uses only the algebra of total division, not global nonvanishing. -/
lemma torsion_rep (b : ℤ) (τ : ℍ) :
    torsionLogDerivative N 0 b τ = 1 / 2 + mSum N b (q τ) / pSum N b (q τ) := by
  rw [mSum_q, pSum_q]
  simp only [torsionLogDerivative, Int.cast_zero, div_eq_mul_inv, mul_inv_rev]
  ring

lemma torsion_cusp_analytic (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) :
    AnalyticAt ℂ (cuspFunction 1 (torsionLogDerivative N 0 b)) 0 := by
  have hG : AnalyticAt ℂ (fun z => (1 / 2 : ℂ) + mSum N b z / pSum N b z) 0 :=
    analyticAt_const.add ((mSum_analytic N b).div (pSum_analytic N b) (pSum_zero_ne N b hb))
  exact hG.congr (cuspFunction_eventually_eq (torsion_rep N b) hG.continuousAt).symm

/-- Taylor coefficients depend only on the actual cusp-function germ. -/
lemma qExpansion_eq_of_cusp_germ {f g : ℍ → ℂ}
    (h : cuspFunction 1 f =ᶠ[𝓝 0] cuspFunction 1 g) : qExpansion 1 f = qExpansion 1 g := by
  ext n
  rw [UpperHalfPlane.qExpansion_coeff, UpperHalfPlane.qExpansion_coeff,
    Filter.EventuallyEq.iteratedDeriv_eq n h]

/-- The product identity is required and proved only as a cusp germ. -/
lemma torsion_product_cusp_germ (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) :
    cuspFunction 1 (torsionLogDerivative N 0 b *
      (fun τ : ℍ => jacobiTheta₂ (shiftedPoint N 0 b τ) τ)) =ᶠ[𝓝 0]
    cuspFunction 1 ((1 / 2 : ℂ) • (fun τ : ℍ => jacobiTheta₂ (shiftedPoint N 0 b τ) τ) +
      (fun τ : ℍ => jacobiTheta₂' (shiftedPoint N 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I))) := by
  let pf : ℍ → ℂ := fun τ => jacobiTheta₂ (shiftedPoint N 0 b τ) τ
  let mf : ℍ → ℂ := fun τ =>
    jacobiTheta₂' (shiftedPoint N 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I)
  have hp : AnalyticAt ℂ (cuspFunction 1 pf) 0 := p_cusp_analytic N b
  have hm : AnalyticAt ℂ (cuspFunction 1 mf) 0 := m_cusp_analytic N b
  have hf := torsion_cusp_analytic N b hb
  have hsp : AnalyticAt ℂ (cuspFunction 1 ((1 / 2 : ℂ) • pf)) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hp.continuousAt]
    exact hp.const_smul
  have hpG : cuspFunction 1 pf =ᶠ[𝓝 0] pSum N b :=
    cuspFunction_eventually_eq (fun τ => (pSum_q N b τ).symm) (pSum_analytic N b).continuousAt
  have hmG : cuspFunction 1 mf =ᶠ[𝓝 0] mSum N b :=
    cuspFunction_eventually_eq (fun τ => (mSum_q N b τ).symm) (mSum_analytic N b).continuousAt
  have hG : AnalyticAt ℂ (fun z => (1 / 2 : ℂ) + mSum N b z / pSum N b z) 0 :=
    analyticAt_const.add ((mSum_analytic N b).div (pSum_analytic N b) (pSum_zero_ne N b hb))
  have hfG : cuspFunction 1 (torsionLogDerivative N 0 b) =ᶠ[𝓝 0]
      (fun z => (1 / 2 : ℂ) + mSum N b z / pSum N b z) :=
    cuspFunction_eventually_eq (torsion_rep N b) hG.continuousAt
  have hpne : ∀ᶠ z in 𝓝 0, pSum N b z ≠ 0 :=
    (pSum_analytic N b).continuousAt.eventually_ne (pSum_zero_ne N b hb)
  change cuspFunction 1 (torsionLogDerivative N 0 b * pf) =ᶠ[𝓝 0]
    cuspFunction 1 ((1 / 2 : ℂ) • pf + mf)
  rw [UpperHalfPlane.cuspFunction_mul hf.continuousAt hp.continuousAt,
    UpperHalfPlane.cuspFunction_add hsp.continuousAt hm.continuousAt,
    UpperHalfPlane.cuspFunction_smul hp.continuousAt]
  filter_upwards [hpG, hmG, hfG, hpne] with z hpz hmz hfz hnez
  change cuspFunction 1 (torsionLogDerivative N 0 b) z * cuspFunction 1 pf z =
    (1 / 2 : ℂ) * cuspFunction 1 pf z + cuspFunction 1 mf z
  rw [hpz, hmz, hfz]
  field_simp [hnez]

/-- At every positive level, the actual torsion quotient has the specified formal expansion. -/
theorem torsion_qExpansion (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) :
    qExpansion 1 (torsionLogDerivative N 0 b) = R (w N b) := by
  let pf : ℍ → ℂ := fun τ => jacobiTheta₂ (shiftedPoint N 0 b τ) τ
  let mf : ℍ → ℂ := fun τ =>
    jacobiTheta₂' (shiftedPoint N 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I)
  have hp : AnalyticAt ℂ (cuspFunction 1 pf) 0 := p_cusp_analytic N b
  have hm : AnalyticAt ℂ (cuspFunction 1 mf) 0 := m_cusp_analytic N b
  have hf := torsion_cusp_analytic N b hb
  have hsp : AnalyticAt ℂ (cuspFunction 1 ((1 / 2 : ℂ) • pf)) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hp.continuousAt]
    exact hp.const_smul
  have hpoint : qExpansion 1 (torsionLogDerivative N 0 b * pf) =
      qExpansion 1 ((1 / 2 : ℂ) • pf + mf) :=
    qExpansion_eq_of_cusp_germ (torsion_product_cusp_germ N b hb)
  have hq : qExpansion 1 (torsionLogDerivative N 0 b) * P (w N b) =
      (1 / 2 : ℂ) • P (w N b) + M (w N b) := by
    rw [← P_qExpansion N b, ← M_qExpansion N b,
      ← UpperHalfPlane.qExpansion_mul hf hp, hpoint,
      UpperHalfPlane.qExpansion_add hsp hm, UpperHalfPlane.qExpansion_smul hp]
  have hC : (1 / 2 : ℂ) • P (w N b) = PowerSeries.C (1 / 2) * P (w N b) := by
    ext n
    simp [smul_eq_mul]
  rw [hC] at hq
  have hmul : (qExpansion 1 (torsionLogDerivative N 0 b) - PowerSeries.C (1 / 2)) * P (w N b) =
      M (w N b) := by linear_combination hq
  have hquot := (PowerSeries.eq_mul_inv_iff_mul_eq (P_constant_ne_zero N b hb)).mpr hmul
  dsimp [R]
  linear_combination hquot

/-- The specified root as an element of the actual level-N coefficient field. -/
def zetaInField : coefficientField N :=
  ⟨zeta N, IntermediateField.mem_adjoin_simple_self ℚ (zeta N)⟩

def wInField (b : ℤ) : coefficientField N := zetaInField N ^ b

lemma wInField_coe (b : ℤ) : (wInField N b : ℂ) = w N b := by
  change (algebraMap (coefficientField N) ℂ) (zetaInField N ^ b) = zeta N ^ b
  rw [map_zpow₀]
  rfl

lemma P_field_constant_ne (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) :
    PowerSeries.constantCoeff (P (wInField N b)) ≠ 0 := by
  intro h
  have h' := congrArg (algebraMap (coefficientField N) ℂ) h
  have hmap : PowerSeries.constantCoeff (P (w N b)) =
      (algebraMap (coefficientField N) ℂ) (PowerSeries.constantCoeff (P (wInField N b))) := by
    rw [← wInField_coe N b]
    change PowerSeries.constantCoeff (P ((algebraMap (coefficientField N) ℂ) (wInField N b))) = _
    rw [← map_P (algebraMap (coefficientField N) ℂ) (wInField N b),
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact P_constant_ne_zero N b hb (by rw [hmap]; simpa using h')

/-- Coefficients of the same formal quotient, computed within the actual coefficient field. -/
def coefficientInField (b : ℤ) (n : ℕ) : coefficientField N := (R (wInField N b)).coeff n

lemma coefficientInField_coe (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) (n : ℕ) :
    (coefficientInField N b n : ℂ) = (qExpansion 1 (torsionLogDerivative N 0 b)).coeff n := by
  rw [torsion_qExpansion N b hb]
  change (algebraMap (coefficientField N) ℂ) ((R (wInField N b)).coeff n) = (R (w N b)).coeff n
  rw [← PowerSeries.coeff_map, map_R (algebraMap (coefficientField N) ℂ) (wInField N b)
    (P_field_constant_ne N b hb)]
  rw [IntermediateField.algebraMap_apply, wInField_coe]

/-- Every coefficient of the actual level-N torsion function lies in its actual cyclotomic field. -/
theorem torsion_coeff_mem (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) (n : ℕ) :
    (qExpansion 1 (torsionLogDerivative N 0 b)).coeff n ∈ coefficientField N := by
  rw [← coefficientInField_coe N b hb n]
  exact (coefficientInField N b n).property

lemma automorphism_w (σ : coefficientField N ≃ₐ[ℚ] coefficientField N) (t b : ℤ)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) :
    σ (wInField N b) = wInField N (t * b) := by
  simp [wInField, hσ, zpow_mul]

lemma coefficientInField_galois (b t : ℤ) (hb : ¬ (N : ℤ) ∣ b)
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) (n : ℕ) :
    σ (coefficientInField N b n) = coefficientInField N (t * b) n := by
  change σ.toRingHom ((R (wInField N b)).coeff n) = (R (wInField N (t * b))).coeff n
  rw [← PowerSeries.coeff_map, map_R σ.toRingHom (wInField N b) (P_field_constant_ne N b hb)]
  rw [show σ.toRingHom (wInField N b) = wInField N (t * b) from automorphism_w N σ t b hσ]

lemma automorphism_admissible (b t : ℤ) (hb : ¬ (N : ℤ) ∣ b)
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) : ¬ (N : ℤ) ∣ t * b := by
  intro htb
  have hwcomplex : w N (t * b) = 1 := (w_eq_one_iff N _).mpr htb
  have hwfield : wInField N (t * b) = 1 := by
    apply Subtype.ext
    change (wInField N (t * b) : ℂ) = 1
    rw [wInField_coe]
    exact hwcomplex
  have hw : wInField N b = 1 := σ.injective (by rw [automorphism_w N σ t b hσ, hwfield, map_one])
  have hw' : w N b = 1 := by
    rw [← wInField_coe N b, hw]
    rfl
  exact hb ((w_eq_one_iff N b).mp hw')

/-- Actual coefficientwise covariance for every positive level, including composite levels. -/
theorem torsion_coeff_galois (b t : ℤ) (hb : ¬ (N : ℤ) ∣ b)
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) (n : ℕ) :
    ((σ ⟨(qExpansion 1 (torsionLogDerivative N 0 b)).coeff n,
        torsion_coeff_mem N b hb n⟩ : coefficientField N) : ℂ) =
      (qExpansion 1 (torsionLogDerivative N 0 (t * b))).coeff n := by
  have hcoef : (⟨(qExpansion 1 (torsionLogDerivative N 0 b)).coeff n,
      torsion_coeff_mem N b hb n⟩ : coefficientField N) = coefficientInField N b n := by
    apply Subtype.ext
    exact (coefficientInField_coe N b hb n).symm
  rw [hcoef, coefficientInField_galois N b t hb σ hσ n]
  exact coefficientInField_coe N (t * b) (automorphism_admissible N b t hb σ hσ) n

lemma complex_root_primitive : IsPrimitiveRoot (zeta N) N :=
  Complex.isPrimitiveRoot_exp N (NeZero.ne N)

lemma field_root_primitive : IsPrimitiveRoot (zetaInField N) N := by
  apply (IsPrimitiveRoot.coe_submonoidClass_iff).mp
  exact complex_root_primitive N

/-- The actual field at every positive level is cyclotomic. -/
instance cyclotomic : IsCyclotomicExtension ({N} : Set ℕ) ℚ (coefficientField N) := by
  apply (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
    (n := N) ℚ ℂ (coefficientField N) (complex_root_primitive N)).mpr
  rfl

instance finiteDimensional : FiniteDimensional ℚ (coefficientField N) :=
  IsCyclotomicExtension.finiteDimensional ({N} : Set ℕ) ℚ (coefficientField N)

instance galois : IsGalois ℚ (coefficientField N) :=
  IsCyclotomicExtension.isGalois ({N} : Set ℕ) ℚ (coefficientField N)

/-- Every automorphism has a bounded root exponent; zero is permitted at level one. -/
theorem automorphism_root_power_nat (σ : coefficientField N ≃ₐ[ℚ] coefficientField N) :
    ∃ t : ℕ, t < N ∧ Nat.Coprime t N ∧ σ (zetaInField N) = zetaInField N ^ t := by
  have hpow : (σ (zetaInField N)) ^ N = 1 := by
    rw [← map_pow, (field_root_primitive N).pow_eq_one, map_one]
  obtain ⟨t, ht, hroot⟩ := (field_root_primitive N).eq_pow_of_pow_eq_one hpow
  have himage : IsPrimitiveRoot (σ (zetaInField N)) N :=
    (field_root_primitive N).map_of_injective σ.injective
  have hcop : Nat.Coprime t N :=
    ((field_root_primitive N).pow_iff_coprime (NeZero.pos N) t).mp (by rw [hroot]; exact himage)
  exact ⟨t, ht, hcop, hroot.symm⟩

/-- A root selector in the integer-power convention of the coefficient theorem. -/
theorem automorphism_root_power_int (σ : coefficientField N ≃ₐ[ℚ] coefficientField N) :
    ∃ t : ℤ, 0 ≤ t ∧ t < N ∧ σ (zetaInField N) = zetaInField N ^ t := by
  obtain ⟨t, ht, _, hroot⟩ := automorphism_root_power_nat N σ
  refine ⟨(t : ℤ), by positivity, by exact_mod_cast ht, ?_⟩
  simpa only [zpow_natCast] using hroot

end ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients
