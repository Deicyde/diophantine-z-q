import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveTorsionDefinitions
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.QExpansion.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Arithmetic of the five-torsion logarithmic derivative

Pairing the positive and negative theta indices gives two ordinary scalar
power series. Their quotient controls the coefficients of the original
analytic torsion logarithmic derivative.
-/

noncomputable section

open Complex UpperHalfPlane Filter
open scoped Topology

namespace ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsionCoefficients

open ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsion

/-- The triangular exponent in the paired theta expansion. -/
def tri (j : ℕ) : ℕ := j * (j + 1) / 2

lemma two_mul_tri (j : ℕ) : 2 * tri j = j * (j + 1) := by
  exact Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one j)

lemma le_tri (j : ℕ) : j ≤ tri j := by
  have h := two_mul_tri j
  nlinarith

lemma tri_injective : Function.Injective tri := by
  intro i j hij
  have hi := two_mul_tri i
  have hj := two_mul_tri j
  rcases lt_trichotomy i j with h | h | h
  · nlinarith
  · exact h
  · nlinarith

lemma tri_zero : tri 0 = 0 := rfl
lemma tri_one : tri 1 = 1 := rfl

section FormalCoefficients

variable {K : Type*} [Field K]

/-- Paired coefficient of the shifted theta denominator. -/
def pPair (w : K) (j : ℕ) : K :=
  (-1) ^ j * (w ^ j - (w ^ (j + 1))⁻¹)

/-- Paired coefficient of the scaled theta derivative. -/
def mPair (w : K) (j : ℕ) : K :=
  (-1) ^ j * ((j : K) * w ^ j + (j + 1 : K) * (w ^ (j + 1))⁻¹)

/-- Extend a triangularly indexed coefficient sequence by zero. -/
def triangularCoeff (c : ℕ → K) (m : ℕ) : K := by
  classical
  exact if h : ∃ j, tri j = m then c h.choose else 0

lemma triangularCoeff_tri (c : ℕ → K) (j : ℕ) :
    triangularCoeff c (tri j) = c j := by
  rw [triangularCoeff, dite_eq_left ⟨j, rfl⟩]
  congr 1
  exact tri_injective (Exists.choose_spec (⟨j, rfl⟩ : ∃ i, tri i = tri j))

lemma triangularCoeff_not_range (c : ℕ → K) (m : ℕ)
    (h : m ∉ Set.range tri) : triangularCoeff c m = 0 := by
  have h' : ¬ ∃ j, tri j = m := h
  rw [triangularCoeff, dite_eq_right h']

/-- The formal denominator series. -/
def P (w : K) : PowerSeries K := PowerSeries.mk (triangularCoeff (pPair w))

/-- The formal scaled-derivative series. -/
def M (w : K) : PowerSeries K := PowerSeries.mk (triangularCoeff (mPair w))

lemma P_coeff_tri (w : K) (j : ℕ) : (P w).coeff (tri j) = pPair w j := by
  simp [P, triangularCoeff_tri]

lemma M_coeff_tri (w : K) (j : ℕ) : (M w).coeff (tri j) = mPair w j := by
  simp [M, triangularCoeff_tri]

lemma P_coeff_zero (w : K) : (P w).coeff 0 = 1 - w⁻¹ := by
  simpa [tri_zero, pPair] using P_coeff_tri w 0

lemma M_coeff_zero (w : K) : (M w).coeff 0 = w⁻¹ := by
  simpa [tri_zero, mPair] using M_coeff_tri w 0

lemma P_coeff_one (w : K) : (P w).coeff 1 = w⁻¹ ^ 2 - w := by
  simpa [tri_one, pPair, inv_pow] using P_coeff_tri w 1

lemma M_coeff_one (w : K) : (M w).coeff 1 = -(w + 2 * w⁻¹ ^ 2) := by
  simpa [tri_one, mPair, inv_pow, one_add_one_eq_two] using M_coeff_tri w 1

end FormalCoefficients

/-- A primitive fifth root of unity in the coefficient field. -/
def zetaFive : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 5)

/-- The torsion coordinate of the integer label. -/
def w (b : ℤ) : ℂ := zetaFive ^ b

/-- The width-one modular parameter. -/
def q (τ : ℍ) : ℂ := Function.Periodic.qParam 1 τ

lemma w_eq_exp (b : ℤ) : w b = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * b / 5) := by
  rw [w, zetaFive, ← Complex.exp_int_mul]
  congr 1
  ring

lemma w_ne_zero (b : ℤ) : w b ≠ 0 := by
  rw [w_eq_exp]
  exact Complex.exp_ne_zero _

lemma norm_w (b : ℤ) : ‖w b‖ = 1 := by
  rw [w_eq_exp, Complex.norm_exp]
  simp

lemma theta_term_nat (b : ℤ) (τ : ℍ) (j : ℕ) :
    jacobiTheta₂_term j (shiftedPoint 0 b τ) τ =
      (-1 : ℂ) ^ j * w b ^ j * q τ ^ tri j := by
  have htri : (2 : ℂ) * (tri j : ℂ) = (j : ℂ) * ((j : ℂ) + 1) := by
    exact_mod_cast two_mul_tri j
  have he : 2 * (Real.pi : ℂ) * Complex.I * j * shiftedPoint 0 b τ +
      (Real.pi : ℂ) * Complex.I * (j : ℂ) ^ 2 * (τ : ℂ) =
      (j : ℂ) * ((Real.pi : ℂ) * Complex.I) +
      (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * b / 5) +
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
    jacobiTheta₂_term (-((j : ℤ) + 1)) (shiftedPoint 0 b τ) τ =
      -(-1 : ℂ) ^ j * (w b ^ (j + 1))⁻¹ * q τ ^ tri j := by
  have htri : (2 : ℂ) * (tri j : ℂ) = (j : ℂ) * ((j : ℂ) + 1) := by
    exact_mod_cast two_mul_tri j
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((-((j : ℤ) + 1) : ℤ) : ℂ) * shiftedPoint 0 b τ +
      (Real.pi : ℂ) * Complex.I * (((-((j : ℤ) + 1) : ℤ) : ℂ)) ^ 2 * (τ : ℂ) =
      -((j + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) +
      -((j + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * b / 5) +
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
    jacobiTheta₂_term j (shiftedPoint 0 b τ) τ +
      jacobiTheta₂_term (-((j : ℤ) + 1)) (shiftedPoint 0 b τ) τ =
      pPair (w b) j * q τ ^ tri j := by
  rw [theta_term_nat, theta_term_neg]
  dsimp [pPair]
  ring

lemma derivative_pair (b : ℤ) (τ : ℍ) (j : ℕ) :
    (j : ℂ) * jacobiTheta₂_term j (shiftedPoint 0 b τ) τ +
      ((-((j : ℤ) + 1) : ℤ) : ℂ) *
        jacobiTheta₂_term (-((j : ℤ) + 1)) (shiftedPoint 0 b τ) τ =
      mPair (w b) j * q τ ^ tri j := by
  rw [theta_term_nat, theta_term_neg]
  dsimp [mPair]
  push_cast
  ring

lemma P_hasSum (b : ℤ) (τ : ℍ) :
    HasSum (fun m : ℕ => (P (w b)).coeff m * q τ ^ m)
      (jacobiTheta₂ (shiftedPoint 0 b τ) τ) := by
  have hp := (hasSum_jacobiTheta₂_term (shiftedPoint 0 b τ) τ.im_pos).nat_add_neg_add_one
  have hp' : HasSum (fun j : ℕ => pPair (w b) j * q τ ^ tri j)
      (jacobiTheta₂ (shiftedPoint 0 b τ) τ) := by
    simpa only [theta_pair] using hp
  apply (tri_injective.hasSum_iff (f := fun m : ℕ => (P (w b)).coeff m * q τ ^ m) ?_).mp
  · change HasSum (fun j : ℕ => (P (w b)).coeff (tri j) * q τ ^ tri j) _
    simpa only [P_coeff_tri] using hp'
  · intro m hm
    simp [P, triangularCoeff_not_range _ _ hm]

lemma M_hasSum (b : ℤ) (τ : ℍ) :
    HasSum (fun m : ℕ => (M (w b)).coeff m * q τ ^ m)
      (jacobiTheta₂' (shiftedPoint 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I)) := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hscaled : HasSum (fun n : ℤ => (n : ℂ) * jacobiTheta₂_term n (shiftedPoint 0 b τ) τ)
      (jacobiTheta₂' (shiftedPoint 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I)) := by
    convert (hasSum_jacobiTheta₂'_term (shiftedPoint 0 b τ) τ.im_pos).div_const
      (2 * (Real.pi : ℂ) * Complex.I) using 1
    ext n
    dsimp [jacobiTheta₂'_term]
    field_simp
  have hm := hscaled.nat_add_neg_add_one
  have hm' : HasSum (fun j : ℕ => mPair (w b) j * q τ ^ tri j)
      (jacobiTheta₂' (shiftedPoint 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I)) := by
    simpa only [Int.cast_natCast, derivative_pair] using hm
  apply (tri_injective.hasSum_iff (f := fun m : ℕ => (M (w b)).coeff m * q τ ^ m) ?_).mp
  · change HasSum (fun j : ℕ => (M (w b)).coeff (tri j) * q τ ^ tri j) _
    simpa only [M_coeff_tri] using hm'
  · intro m hm
    simp [M, triangularCoeff_not_range _ _ hm]

lemma P_coeff_norm_le_two (b : ℤ) (m : ℕ) : ‖(P (w b)).coeff m‖ ≤ 2 := by
  classical
  rw [P, PowerSeries.coeff_mk, triangularCoeff]
  split_ifs with h
  · dsimp [pPair]
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc
      ‖w b ^ h.choose - (w b ^ (h.choose + 1))⁻¹‖ ≤
          ‖w b ^ h.choose‖ + ‖(w b ^ (h.choose + 1))⁻¹‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, norm_w, norm_inv]
  · simp

lemma M_coeff_norm_le (b : ℤ) (m : ℕ) : ‖(M (w b)).coeff m‖ ≤ 2 * m + 1 := by
  classical
  rw [M, PowerSeries.coeff_mk, triangularCoeff]
  split_ifs with h
  · have hj : h.choose ≤ m := (le_tri h.choose).trans_eq h.choose_spec
    dsimp [mPair]
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc
      ‖(h.choose : ℂ) * w b ^ h.choose +
          (h.choose + 1 : ℂ) * (w b ^ (h.choose + 1))⁻¹‖ ≤
          ‖(h.choose : ℂ) * w b ^ h.choose‖ +
          ‖(h.choose + 1 : ℂ) * (w b ^ (h.choose + 1))⁻¹‖ := norm_add_le _ _
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
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ (fun m => (P (w b)).coeff m)).radius := by
  apply FormalMultilinearSeries.le_radius_of_bound _ 2 (r := 1)
  intro m
  simpa only [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow, mul_one]
    using P_coeff_norm_le_two b m

lemma M_radius (b : ℤ) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ (fun m => (M (w b)).coeff m)).radius := by
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
    (fun m => mul_le_mul_of_nonneg_right (M_coeff_norm_le b m) (by positivity)) hs

/-- Scalar sums associated with the two paired series. -/
def pSum (b : ℤ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (fun m => (P (w b)).coeff m)

def mSum (b : ℤ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (fun m => (M (w b)).coeff m)

lemma pSum_analytic (b : ℤ) : AnalyticAt ℂ (pSum b) 0 :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall _ (zero_lt_one.trans_le (P_radius b))).analyticAt

lemma mSum_analytic (b : ℤ) : AnalyticAt ℂ (mSum b) 0 :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall _ (zero_lt_one.trans_le (M_radius b))).analyticAt

lemma pSum_q (b : ℤ) (τ : ℍ) :
    pSum b (q τ) = jacobiTheta₂ (shiftedPoint 0 b τ) τ := by
  rw [pSum, FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul] using (P_hasSum b τ).tsum_eq

lemma mSum_q (b : ℤ) (τ : ℍ) :
    mSum b (q τ) = jacobiTheta₂' (shiftedPoint 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [mSum, FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul] using (M_hasSum b τ).tsum_eq

lemma pSum_zero (b : ℤ) : pSum b 0 = 1 - (w b)⁻¹ := by
  simp [pSum, FormalMultilinearSeries.ofScalarsSum_zero, P_coeff_zero]

lemma mSum_zero (b : ℤ) : mSum b 0 = (w b)⁻¹ := by
  simp [mSum, FormalMultilinearSeries.ofScalarsSum_zero, M_coeff_zero]

/-- A local scalar representation gives the actual cusp function, including its value at zero. -/
lemma cuspFunction_eventually_eq {f : ℍ → ℂ} {G : ℂ → ℂ}
    (hrep : ∀ τ : ℍ, f τ = G (q τ)) (hG : ContinuousAt G 0) :
    cuspFunction 1 f =ᶠ[𝓝 0] G := by
  have hnonzero : ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → cuspFunction 1 f z = G z := by
    intro z hz hz1
    rw [UpperHalfPlane.cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hz]
    have him : 0 < (Function.Periodic.invQParam 1 z).im :=
      Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hz1 hz
    change f (ofComplex (Function.Periodic.invQParam 1 z)) = G z
    rw [hrep]
    congr 1
    rw [q, ofComplex_apply_of_im_pos him]
    exact Function.Periodic.qParam_right_inv one_ne_zero hz
  have hball : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 := by
    change {z : ℂ | ‖z‖ < 1} ∈ 𝓝 0
    have hs : {z : ℂ | ‖z‖ < 1} = Metric.ball 0 1 := by ext z; simp
    rw [hs]
    exact Metric.ball_mem_nhds (0 : ℂ) one_pos
  have hpunct : cuspFunction 1 f =ᶠ[𝓝[≠] 0] G := by
    filter_upwards [hball.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz0
    exact hnonzero z hz0 hz
  have hzero : cuspFunction 1 f 0 = G 0 := by
    change Function.Periodic.cuspFunction 1 (f ∘ ofComplex) 0 = G 0
    rw [Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
    exact ((hG.tendsto.mono_left nhdsWithin_le_nhds).congr' hpunct.symm).limUnder_eq
  filter_upwards [hball] with z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · exact hzero
  · exact hnonzero z hz0 hz

lemma p_cusp_analytic (b : ℤ) :
    AnalyticAt ℂ (cuspFunction 1 (fun τ : ℍ => jacobiTheta₂ (shiftedPoint 0 b τ) τ)) 0 :=
  (pSum_analytic b).congr (cuspFunction_eventually_eq (fun τ => (pSum_q b τ).symm)
    (pSum_analytic b).continuousAt).symm

lemma m_cusp_analytic (b : ℤ) :
    AnalyticAt ℂ (cuspFunction 1 (fun τ : ℍ =>
      jacobiTheta₂' (shiftedPoint 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I))) 0 :=
  (mSum_analytic b).congr (cuspFunction_eventually_eq (fun τ => (mSum_q b τ).symm)
    (mSum_analytic b).continuousAt).symm

lemma P_qExpansion (b : ℤ) :
    qExpansion 1 (fun τ : ℍ => jacobiTheta₂ (shiftedPoint 0 b τ) τ) = P (w b) := by
  ext m
  symm
  exact TauCeti.UpperHalfPlane.qExpansion_coeff_unique
    (c := fun n => (P (w b)).coeff n) one_pos (p_cusp_analytic b)
    (fun τ => by simpa only [q, smul_eq_mul] using P_hasSum b τ) m

lemma M_qExpansion (b : ℤ) :
    qExpansion 1 (fun τ : ℍ =>
      jacobiTheta₂' (shiftedPoint 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I)) = M (w b) := by
  ext m
  symm
  exact TauCeti.UpperHalfPlane.qExpansion_coeff_unique
    (c := fun n => (M (w b)).coeff n) one_pos (m_cusp_analytic b)
    (fun τ => by simpa only [q, smul_eq_mul] using M_hasSum b τ) m

lemma w_eq_one_iff (b : ℤ) : w b = 1 ↔ (5 : ℤ) ∣ b := by
  let u : ℂˣ := Units.mk0 zetaFive (Complex.exp_ne_zero _)
  have hprim : IsPrimitiveRoot u 5 := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    exact Complex.isPrimitiveRoot_exp 5 (by decide)
  have h := hprim.zpow_eq_one_iff_dvd b
  constructor
  · intro hb
    apply h.mp
    apply Units.ext
    simp only [Units.val_zpow_eq_zpow_val, Units.val_one]
    change zetaFive ^ b = 1
    exact hb
  · intro hb
    have h' := congrArg Units.val (h.mpr hb)
    simp only [Units.val_zpow_eq_zpow_val, Units.val_one] at h'
    change zetaFive ^ b = 1 at h'
    exact h'

lemma P_constant_ne_zero (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) :
    PowerSeries.constantCoeff (P (w b)) ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, P_coeff_zero]
  intro h
  have hi : (w b)⁻¹ = 1 := by linear_combination -h
  have hw : w b = 1 := by simpa using congrArg Inv.inv hi
  exact hb ((w_eq_one_iff b).mp hw)

lemma pSum_zero_ne (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) : pSum b 0 ≠ 0 := by
  simpa only [pSum_zero, ← P_coeff_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    using P_constant_ne_zero b hb

lemma torsion_rep (b : ℤ) (τ : ℍ) :
    torsionLogDerivative 0 b τ = 1 / 2 + mSum b (q τ) / pSum b (q τ) := by
  rw [mSum_q, pSum_q]
  simp only [torsionLogDerivative, Int.cast_zero,
    div_eq_mul_inv, mul_inv_rev]
  ring

lemma torsion_cusp_analytic (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) :
    AnalyticAt ℂ (cuspFunction 1 (torsionLogDerivative 0 b)) 0 := by
  have hG : AnalyticAt ℂ (fun z => (1 / 2 : ℂ) + mSum b z / pSum b z) 0 :=
    analyticAt_const.add ((mSum_analytic b).div (pSum_analytic b) (pSum_zero_ne b hb))
  exact hG.congr (cuspFunction_eventually_eq (torsion_rep b) hG.continuousAt).symm

/-- The formal arithmetic quotient of the two triangular series. -/
def R {K : Type*} [Field K] (v : K) : PowerSeries K :=
  PowerSeries.C (1 / 2) + M v * (P v)⁻¹

/-- The actual analytic torsion quotient has precisely the formal quotient expansion. -/
theorem torsion_qExpansion (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) :
    qExpansion 1 (torsionLogDerivative 0 b) = R (w b) := by
  let pf : ℍ → ℂ := fun τ => jacobiTheta₂ (shiftedPoint 0 b τ) τ
  let mf : ℍ → ℂ := fun τ =>
    jacobiTheta₂' (shiftedPoint 0 b τ) τ / (2 * (Real.pi : ℂ) * Complex.I)
  have hp : AnalyticAt ℂ (cuspFunction 1 pf) 0 := p_cusp_analytic b
  have hm : AnalyticAt ℂ (cuspFunction 1 mf) 0 := m_cusp_analytic b
  have hf := torsion_cusp_analytic b hb
  have hpoint : torsionLogDerivative 0 b * pf = (1 / 2 : ℂ) • pf + mf := by
    ext τ
    have hp0 : pf τ ≠ 0 :=
      ZInQ.Contrib.HeckePrimeRationality.ThetaFive.jacobiTheta₂_fiveTorsion_ne_zero τ 0 b
        (by simpa using hb)
    have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      torsionLogDerivative, Int.cast_zero, zero_div, zero_add]
    dsimp [pf, mf]
    dsimp [pf] at hp0
    field_simp [hp0, hc]
  have hsp : AnalyticAt ℂ (cuspFunction 1 ((1 / 2 : ℂ) • pf)) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hp.continuousAt]
    exact hp.const_smul
  have hq : qExpansion 1 (torsionLogDerivative 0 b) * P (w b) =
      (1 / 2 : ℂ) • P (w b) + M (w b) := by
    rw [← P_qExpansion b, ← M_qExpansion b,
      ← UpperHalfPlane.qExpansion_mul hf hp, hpoint,
      UpperHalfPlane.qExpansion_add hsp hm, UpperHalfPlane.qExpansion_smul hp]
  have hC : (1 / 2 : ℂ) • P (w b) = PowerSeries.C (1 / 2) * P (w b) := by
    ext n
    simp [smul_eq_mul]
  rw [hC] at hq
  have hmul : (qExpansion 1 (torsionLogDerivative 0 b) - PowerSeries.C (1 / 2)) * P (w b) =
      M (w b) := by linear_combination hq
  have hquot := (PowerSeries.eq_mul_inv_iff_mul_eq (P_constant_ne_zero b hb)).mpr hmul
  dsimp [R]
  linear_combination hquot

section FieldMaps

variable {K L : Type*} [Field K] [Field L]

lemma map_pPair (φ : K →+* L) (v : K) (j : ℕ) : φ (pPair v j) = pPair (φ v) j := by
  simp [pPair]

lemma map_mPair (φ : K →+* L) (v : K) (j : ℕ) : φ (mPair v j) = mPair (φ v) j := by
  simp [mPair]

lemma map_P (φ : K →+* L) (v : K) : PowerSeries.map φ (P v) = P (φ v) := by
  classical
  ext m
  simp only [PowerSeries.coeff_map, P, PowerSeries.coeff_mk, triangularCoeff]
  split_ifs <;> simp [map_pPair]

lemma map_M (φ : K →+* L) (v : K) : PowerSeries.map φ (M v) = M (φ v) := by
  classical
  ext m
  simp only [PowerSeries.coeff_map, M, PowerSeries.coeff_mk, triangularCoeff]
  split_ifs <;> simp [map_mPair]

lemma map_P_inverse (φ : K →+* L) (v : K)
    (hv : PowerSeries.constantCoeff (P v) ≠ 0) :
    PowerSeries.map φ ((P v)⁻¹) = (P (φ v))⁻¹ := by
  have hmap : PowerSeries.constantCoeff (P (φ v)) ≠ 0 := by
    rw [← map_P φ v, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact fun h => hv (φ.injective (by simpa using h))
  apply (PowerSeries.eq_inv_iff_mul_eq_one hmap).mpr
  rw [← map_P φ v, ← map_mul, PowerSeries.inv_mul_cancel _ hv, map_one]

lemma map_R (φ : K →+* L) (v : K)
    (hv : PowerSeries.constantCoeff (P v) ≠ 0) :
    PowerSeries.map φ (R v) = R (φ v) := by
  simp only [R, map_add, PowerSeries.map_C, map_mul, map_M, map_P_inverse φ v hv]
  simp
  have htwo : φ (2 : K) = (2 : L) := by
    simpa only [one_add_one_eq_two, map_one] using φ.map_add (1 : K) 1
  rw [htwo]

end FieldMaps

/-- The explicitly generated cyclotomic coefficient field. -/
def KFive : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaFive}

/-- The distinguished root as an element of that field. -/
def zetaInField : KFive :=
  ⟨zetaFive, IntermediateField.mem_adjoin_simple_self ℚ zetaFive⟩

def wInField (b : ℤ) : KFive := zetaInField ^ b

lemma wInField_coe (b : ℤ) : (wInField b : ℂ) = w b := by
  change (algebraMap KFive ℂ) (zetaInField ^ b) = zetaFive ^ b
  rw [map_zpow₀]
  rfl

lemma P_field_constant_ne (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) :
    PowerSeries.constantCoeff (P (wInField b)) ≠ 0 := by
  intro h
  have h' := congrArg (algebraMap KFive ℂ) h
  have hmap : PowerSeries.constantCoeff (P (w b)) =
      (algebraMap KFive ℂ) (PowerSeries.constantCoeff (P (wInField b))) := by
    rw [← wInField_coe b]
    change PowerSeries.constantCoeff (P ((algebraMap KFive ℂ) (wInField b))) = _
    rw [← map_P (algebraMap KFive ℂ) (wInField b),
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact P_constant_ne_zero b hb (by rw [hmap]; simpa using h')

/-- A canonical coefficient lift, computed inside the generated field. -/
def coefficientInField (b : ℤ) (n : ℕ) : KFive := (R (wInField b)).coeff n

lemma coefficientInField_coe (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) (n : ℕ) :
    (coefficientInField b n : ℂ) = (qExpansion 1 (torsionLogDerivative 0 b)).coeff n := by
  rw [torsion_qExpansion b hb]
  change (algebraMap KFive ℂ) ((R (wInField b)).coeff n) = (R (w b)).coeff n
  rw [← PowerSeries.coeff_map, map_R (algebraMap KFive ℂ) (wInField b)
    (P_field_constant_ne b hb)]
  rw [IntermediateField.algebraMap_apply, wInField_coe]

/-- Every coefficient of the actual torsion function lies in the fifth cyclotomic field. -/
theorem torsion_coeff_mem (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) (n : ℕ) :
    (qExpansion 1 (torsionLogDerivative 0 b)).coeff n ∈ KFive := by
  rw [← coefficientInField_coe b hb n]
  exact (coefficientInField b n).property

lemma automorphism_w (σ : KFive ≃ₐ[ℚ] KFive) (t b : ℤ)
    (hσ : σ zetaInField = zetaInField ^ t) :
    σ (wInField b) = wInField (t * b) := by
  simp [wInField, hσ, zpow_mul]

lemma coefficientInField_galois (b t : ℤ) (hb : ¬ (5 : ℤ) ∣ b)
    (σ : KFive ≃ₐ[ℚ] KFive) (hσ : σ zetaInField = zetaInField ^ t) (n : ℕ) :
    σ (coefficientInField b n) = coefficientInField (t * b) n := by
  change σ.toRingHom ((R (wInField b)).coeff n) = (R (wInField (t * b))).coeff n
  rw [← PowerSeries.coeff_map, map_R σ.toRingHom (wInField b) (P_field_constant_ne b hb)]
  rw [show σ.toRingHom (wInField b) = wInField (t * b) from automorphism_w σ t b hσ]

lemma automorphism_admissible (b t : ℤ) (hb : ¬ (5 : ℤ) ∣ b)
    (σ : KFive ≃ₐ[ℚ] KFive) (hσ : σ zetaInField = zetaInField ^ t) :
    ¬ (5 : ℤ) ∣ t * b := by
  intro htb
  have hwcomplex : w (t * b) = 1 := (w_eq_one_iff _).mpr htb
  have hwfield : wInField (t * b) = 1 := by
    apply Subtype.ext
    change (wInField (t * b) : ℂ) = 1
    rw [wInField_coe]
    exact hwcomplex
  have hw : wInField b = 1 := σ.injective (by rw [automorphism_w σ t b hσ, hwfield, map_one])
  have hw' : w b = 1 := by
    rw [← wInField_coe b, hw]
    rfl
  exact hb ((w_eq_one_iff b).mp hw')

/-- Coefficientwise Galois covariance of the original analytic torsion function. -/
theorem torsion_coeff_galois (b t : ℤ) (hb : ¬ (5 : ℤ) ∣ b)
    (σ : KFive ≃ₐ[ℚ] KFive) (hσ : σ zetaInField = zetaInField ^ t) (n : ℕ) :
    ((σ ⟨(qExpansion 1 (torsionLogDerivative 0 b)).coeff n,
        torsion_coeff_mem b hb n⟩ : KFive) : ℂ) =
      (qExpansion 1 (torsionLogDerivative 0 (t * b))).coeff n := by
  have hcoef : (⟨(qExpansion 1 (torsionLogDerivative 0 b)).coeff n,
      torsion_coeff_mem b hb n⟩ : KFive) = coefficientInField b n := by
    apply Subtype.ext
    exact (coefficientInField_coe b hb n).symm
  rw [hcoef, coefficientInField_galois b t hb σ hσ n]
  exact coefficientInField_coe (t * b) (automorphism_admissible b t hb σ hσ) n

lemma R_mul_P (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) :
    R (w b) * P (w b) = PowerSeries.C (1 / 2) * P (w b) + M (w b) := by
  dsimp [R]
  rw [add_mul, mul_assoc, PowerSeries.inv_mul_cancel _ (P_constant_ne_zero b hb), mul_one]

lemma R_coeff_zero (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) :
    (R (w b)).coeff 0 = (w b + 1) / (2 * (w b - 1)) := by
  have hP : PowerSeries.constantCoeff (P (w b)) = 1 - (w b)⁻¹ := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, P_coeff_zero]
  have hM : PowerSeries.constantCoeff (M (w b)) = (w b)⁻¹ := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, M_coeff_zero]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [R, map_add, map_mul, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_inv, hP, hM]
  have hw0 := w_ne_zero b
  have hw1 : w b ≠ 1 := fun h => hb ((w_eq_one_iff b).mp h)
  field_simp [hw0, hw1]
  ring

lemma R_coeff_one (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) :
    (R (w b)).coeff 1 = (w b)⁻¹ - w b := by
  have h1 := congrArg (PowerSeries.coeff 1) (R_mul_P b hb)
  simp only [PowerSeries.coeff_one_mul, map_add, PowerSeries.coeff_C_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, P_coeff_zero, R_coeff_zero b hb,
    P_coeff_one, M_coeff_one] at h1
  have hp0 : (1 : ℂ) - (w b)⁻¹ ≠ 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, P_coeff_zero]
      using P_constant_ne_zero b hb
  apply mul_right_cancel₀ hp0
  calc
    (R (w b)).coeff 1 * (1 - (w b)⁻¹) =
        (1 / 2 : ℂ) * ((w b)⁻¹ ^ 2 - w b) - (w b + 2 * (w b)⁻¹ ^ 2) -
          ((w b)⁻¹ ^ 2 - w b) * ((w b + 1) / (2 * (w b - 1))) := by
      linear_combination h1
    _ = ((w b)⁻¹ - w b) * (1 - (w b)⁻¹) := by
      have hw0 := w_ne_zero b
      have hw1 : w b ≠ 1 := fun h => hb ((w_eq_one_iff b).mp h)
      field_simp [hw0, hw1]
      ring

/-- The constant term of the actual torsion logarithmic derivative. -/
theorem torsion_coeff_zero (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) :
    (qExpansion 1 (torsionLogDerivative 0 b)).coeff 0 =
      (w b + 1) / (2 * (w b - 1)) := by
  rw [torsion_qExpansion b hb]
  exact R_coeff_zero b hb

/-- The first nonconstant coefficient of the actual torsion logarithmic derivative. -/
theorem torsion_coeff_one (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) :
    (qExpansion 1 (torsionLogDerivative 0 b)).coeff 1 = (w b)⁻¹ - w b := by
  rw [torsion_qExpansion b hb]
  exact R_coeff_one b hb

end ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsionCoefficients
