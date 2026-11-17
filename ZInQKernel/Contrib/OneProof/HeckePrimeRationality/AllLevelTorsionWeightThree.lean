import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelEisensteinWeightTwoBounds
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionMuFourierFinite

/-!
# Actual weight-three torsion values and the third theta-kernel coefficient

The weight-three value is the actual derivative of the Weierstrass lattice
function, with the zero-class convention. Its inverse-cube lattice sum is
absolutely convergent. Third coefficients below are derived by ordinary
analytic differentiation of the existing theta-kernel unit.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open Complex Filter Function
open scoped Topology Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionWeightThree

open ZInQ.Contrib.HeckePrimeRationality
open CompletedTheta TorsionWeierstrassData TorsionMuFourierKernel

/-- The actual Weierstrass derivative at a torsion point, zero on the bad label class. -/
def yValue (N : _root_.Nat) (a b : _root_.Int) (τ : _root_.UpperHalfPlane) : _root_.Complex :=
  if (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b then 0 else
    (ThetaWeierstrass.periodPair τ).derivWeierstrassP (torsionPoint N a b τ)

theorem yValue_of_good (N : ℕ) (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    yValue N a b τ = (ThetaWeierstrass.periodPair τ).derivWeierstrassP (torsionPoint N a b τ) := by
  simp only [yValue, ite_eq_right hg]

theorem yValue_of_bad (N : ℕ) (a b : ℤ) (τ : ℍ)
    (hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) : yValue N a b τ = 0 := by
  simp only [yValue, ite_eq_left hb]

theorem yValue_eq_actual (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    yValue N a b τ = (ThetaWeierstrass.periodPair τ).derivWeierstrassP (torsionPoint N a b τ) := by
  by_cases hg : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · rw [yValue_of_bad N a b τ hg]
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    obtain ⟨m, hm⟩ := hg.1
    obtain ⟨n, hn⟩ := hg.2
    have hl : torsionPoint N a b τ ∈ (ThetaWeierstrass.periodPair τ).lattice := by
      rw [ThetaWeierstrass.mem_periodPair_lattice_iff]
      refine ⟨n, m, ?_⟩
      unfold torsionPoint
      rw [hm, hn]
      push_cast
      field_simp
      ring
    exact ((ThetaWeierstrass.periodPair τ).derivWeierstrassP_coe ⟨_, hl⟩).symm
  · exact yValue_of_good N a b τ hg

theorem yValue_zero (N : ℕ) (τ : ℍ) : yValue N 0 0 τ = 0 := by simp [yValue]

theorem yValue_neg (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    yValue N (-a) (-b) τ = -yValue N a b τ := by
  rw [yValue_eq_actual N hN, yValue_eq_actual N hN]
  have heq : torsionPoint N (-a) (-b) τ = -torsionPoint N a b τ := by
    unfold torsionPoint
    push_cast
    ring
  rw [heq, PeriodPair.derivWeierstrassP_neg]

theorem yValue_shift (N : ℕ) (hN : 0 < N) (a b m n : ℤ) (τ : ℍ) :
    yValue N (a + N * m) (b + N * n) τ = yValue N a b τ := by
  rw [yValue_eq_actual N hN, yValue_eq_actual N hN,
    EisensteinWeightTwo.torsionPoint_add_level N hN]
  have hl : (m : ℂ) * (τ : ℂ) + (n : ℂ) ∈ (ThetaWeierstrass.periodPair τ).lattice :=
    (ThetaWeierstrass.mem_periodPair_lattice_iff τ _).mpr ⟨n, m, by ring⟩
  exact (ThetaWeierstrass.periodPair τ).derivWeierstrassP_add_coe _ ⟨_, hl⟩

/-- The absolutely convergent shifted inverse-cube sum is the actual Weierstrass derivative. -/
theorem hasSum_inverseCube (τ : ℍ) (z : ℂ) :
    HasSum (fun p : ℤ × ℤ => 1 / (z + (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)) ^ 3)
      (-(1 / 2 : ℂ) * (ThetaWeierstrass.periodPair τ).derivWeierstrassP z) := by
  have h := (ThetaWeierstrass.periodPair τ).hasSum_derivWeierstrassP (-z)
  rw [PeriodPair.derivWeierstrassP_neg] at h
  have hg := (EisensteinWeightTwo.gridEquiv τ).hasSum_iff.mpr h
  have hs := hg.div_const (2 : ℂ)
  have hv : -(ThetaWeierstrass.periodPair τ).derivWeierstrassP z / 2 =
      -(1 / 2 : ℂ) * (ThetaWeierstrass.periodPair τ).derivWeierstrassP z := by ring
  rw [hv] at hs
  refine hs.congr_fun ?_
  intro p
  simp only [Function.comp_apply, EisensteinWeightTwo.gridEquiv_coe]
  rw [show -z - ((p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)) =
      -(z + (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)) by ring]
  generalize z + (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ) = w
  rw [show (-w) ^ 3 = -(w ^ 3) by ring]
  simp [div_eq_mul_inv]
  ring

lemma inverseCube_congruence (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) (p : ℤ × ℤ) :
    1 / (torsionPoint N a b τ + (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)) ^ 3 =
      (N : ℂ) ^ 3 * EisensteinSeries.eisSummand 3 ![a + N * p.1, b + N * p.2] τ := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have heq : torsionPoint N a b τ + (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ) =
      ((((a + N * p.1 : ℤ) : ℂ) * (τ : ℂ) + ((b + N * p.2 : ℤ) : ℂ)) / (N : ℂ)) := by
    unfold torsionPoint
    push_cast
    field_simp
    ring
  rw [heq]
  simp only [EisensteinSeries.eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, _root_.zpow_neg, _root_.zpow_ofNat, div_pow, one_div, inv_div]
  rfl

/-- Actual weight-three congruence terms are absolutely summable on the full grid. -/
theorem hasSum_weightThree_congruence (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    HasSum (fun p : ℤ × ℤ => EisensteinSeries.eisSummand 3 ![a + N * p.1, b + N * p.2] τ)
      (-(1 / 2 : ℂ) * yValue N a b τ / (N : ℂ) ^ 3) := by
  have hNc : (N : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')
  rw [yValue_eq_actual N hN]
  refine ((hasSum_inverseCube τ (torsionPoint N a b τ)).div_const ((N : ℂ) ^ 3)).congr_fun ?_
  intro p
  rw [inverseCube_congruence N hN]
  exact (mul_div_cancel_left₀ _ hNc).symm

/-- The actual all-label derivative value equals minus twice the genuine weight-three Eisenstein sum. -/
theorem yValue_eq_eisenstein_sum (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    yValue N a b τ = (-2 : ℂ) * (N : ℂ) ^ 3 * ∑' p : ℤ × ℤ,
      EisensteinSeries.eisSummand 3 ![a + N * p.1, b + N * p.2] τ := by
  rw [(hasSum_weightThree_congruence N hN a b τ).tsum_eq]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp [hNc]

/-- The genuine cubic expression whose Fourier correction determines the derivative value. -/
def cubicValue (N : ℕ) (a b : ℤ) (τ : ℍ) : ℂ :=
  lambdaValue N a b τ ^ 3 - 3 * lambdaValue N a b τ * xValue N a b τ

/-- A normalized logarithmic-derivative third-jet identity for an actual analytic function. -/
theorem analytic_third_jet {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0) :
    iteratedDeriv 3 F 0 = F 0 *
      ((logDeriv F 0) ^ 3 + 3 * logDeriv F 0 * deriv (logDeriv F) 0 +
        iteratedDeriv 2 (logDeriv F) 0) := by
  have hL : AnalyticAt ℂ (logDeriv F) 0 := hF.deriv.div hF h0
  have heq : deriv F =ᶠ[𝓝 (0 : ℂ)] (fun z => logDeriv F z * F z) := by
    filter_upwards [hF.continuousAt.eventually_ne h0] with z hz
    simp [logDeriv, hz]
  have h1 : deriv F 0 = logDeriv F 0 * F 0 := by simp [logDeriv, h0]
  have h2 := heq.iteratedDeriv_eq 1
  rw [iteratedDeriv_one, iteratedDeriv_fun_mul hL.contDiffAt hF.contDiffAt] at h2
  simp only [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one] at h2
  norm_num at h2
  have h3 := heq.iteratedDeriv_eq 2
  rw [iteratedDeriv_fun_mul hL.contDiffAt hF.contDiffAt] at h3
  simp only [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one] at h3
  norm_num at h3
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h3 ⊢
  linear_combination h3 + logDeriv F 0 * h2 +
    (logDeriv F 0 ^ 2 + 2 * deriv (logDeriv F) 0) * h1

/-! ## Actual logarithmic jets of the analytic kernel unit -/

theorem unitLog_odd (τ : ℍ) :
    Function.Odd (ThetaWeierstrass.unitLogDerivative (H τ) 0) := by
  let A := ThetaWeierstrass.dividedTheta τ
  have he : (fun z : ℂ => A (-z)) = A := funext (ThetaWeierstrass.dividedTheta_even τ)
  have hd (z : ℂ) : deriv A (-z) = -deriv A z := by
    have h := deriv_comp_neg A z
    rw [he] at h
    linear_combination h
  intro z
  change deriv A (-z) / A (-z) = -(deriv A z / A z)
  rw [hd, show A (-z) = A z from ThetaWeierstrass.dividedTheta_even τ z]
  ring

theorem unitLog_second_zero (τ : ℍ) :
    iteratedDeriv 2 (ThetaWeierstrass.unitLogDerivative (H τ) 0) 0 = 0 := by
  let U := ThetaWeierstrass.unitLogDerivative (H τ) 0
  have he : (fun z : ℂ => U (-z)) = fun z => -U z := funext (unitLog_odd τ)
  have h := iteratedDeriv_comp_neg 2 U (0 : ℂ)
  rw [he] at h
  simp only [iteratedDeriv_fun_neg, neg_zero] at h
  norm_num at h
  linear_combination -h / 2

theorem H_log_neg (τ : ℍ) (z : ℂ) : logDeriv (H τ) (-z) = -logDeriv (H τ) z := by
  simp only [logDeriv, Pi.div_apply, deriv_H, TorsionFourierKernel.Hder_neg, H_neg, div_neg]

theorem wp_deriv_eq_neg_log_second (τ : ℍ) {z : ℂ}
    (hz : H τ z ≠ 0) :
    (ThetaWeierstrass.periodPair τ).derivWeierstrassP z =
      -iteratedDeriv 2 (logDeriv (H τ)) z := by
  have heq : (ThetaWeierstrass.periodPair τ).weierstrassP =ᶠ[𝓝 z]
      (fun w => -deriv (logDeriv (H τ)) w + ThetaWeierstrass.finitePart τ) := by
    filter_upwards [(differentiable_H τ z).continuousAt.eventually_ne hz] with w hw
    exact ThetaWeierstrass.weierstrassP_eq_neg_deriv_logDerivative τ w
      (fun hl => hw ((ThetaWeierstrass.H_zero_iff_mem_lattice τ w).mpr hl))
  have hd := heq.deriv_eq
  rw [PeriodPair.deriv_weierstrassP] at hd
  have hL : AnalyticAt ℂ (logDeriv (H τ)) z :=
    ((differentiable_H τ).analyticAt z).deriv.div ((differentiable_H τ).analyticAt z) hz
  have hneg := (hL.deriv.differentiableAt.hasDerivAt.fun_neg.add_const
    (ThetaWeierstrass.finitePart τ)).deriv
  have hres := hd.trans hneg
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hres

/-- Local affine differentiation requires analyticity only at the actual image point. -/
theorem deriv_affine {F : ℂ → ℂ} (k u z : ℂ) (hF : AnalyticAt ℂ F (k * z + u)) :
    deriv (fun w => F (k * w + u)) z = k * deriv F (k * z + u) := by
  have hi : HasDerivAt (fun w : ℂ => k * w + u) k z := by
    simpa using! ((hasDerivAt_id z).const_mul k).add_const u
  simpa only [Function.comp_def, mul_comm] using! (hF.differentiableAt.hasDerivAt.comp z hi).deriv

theorem second_affine {F : ℂ → ℂ} (k u : ℂ) (hF : AnalyticAt ℂ F u) :
    iteratedDeriv 2 (fun w => F (k * w + u)) 0 = k ^ 2 * iteratedDeriv 2 F u := by
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ F (k * z + u) := by
    have ht : Tendsto (fun z : ℂ => k * z + u) (𝓝 0) (𝓝 u) := by
      simpa only [Pi.add_apply, Pi.mul_apply, id_eq, mul_zero, zero_add] using!
        (continuous_const.mul continuous_id |>.add continuous_const).tendsto (0 : ℂ)
    exact ht.eventually hF.eventually_analyticAt
  have heq : deriv (fun w => F (k * w + u)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => k * deriv F (k * z + u)) := hn.mono fun z hz => deriv_affine k u z hz
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [heq.deriv_eq, deriv_const_mul_field, deriv_affine k u 0 (by simpa using hF.deriv)]
  simp
  ring

theorem kernelUnit_log (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) (z : ℂ)
    (hp : H τ ((N : ℂ) * z - torsionPoint N a b τ) ≠ 0)
    (hA : ThetaWeierstrass.dividedTheta τ ((N : ℂ) * z) ≠ 0) :
    logDeriv (kernelUnit N a b τ) z = scale * (a : ℂ) +
      (N : ℂ) * logDeriv (H τ) ((N : ℂ) * z - torsionPoint N a b τ) -
      (N : ℂ) * ThetaWeierstrass.unitLogDerivative (H τ) 0 ((N : ℂ) * z) := by
  let p := torsionPoint N a b τ
  let C : ℂ := Hder τ 0 / H τ (-p)
  have hC : C ≠ 0 := div_ne_zero (TorsionFourierKernel.Hder_zero_ne τ)
    (TorsionFourierKernel.H_minus_torsion_ne N a b τ hg)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hn : TorsionFourierComparison.kernelNumerator N a b τ =
      (fun w : ℂ => C * (cexp (scale * (a : ℂ) * w) * H τ ((N : ℂ) * w - p))) := by
    funext w
    simp only [TorsionFourierComparison.kernelNumerator, C, p, scale]
    ring
  have he : logDeriv (fun w : ℂ => cexp (scale * (a : ℂ) * w)) z = scale * (a : ℂ) := by
    have h := ((hasDerivAt_id z).const_mul (scale * (a : ℂ))).cexp.deriv
    change deriv (fun w : ℂ => cexp (scale * (a : ℂ) * w)) z = _ at h
    rw [logDeriv, Pi.div_apply, h]
    simpa only [id_eq, mul_one] using mul_div_cancel_left₀ (scale * (a : ℂ))
      (Complex.exp_ne_zero (scale * (a : ℂ) * z))
  have hH : Differentiable ℂ (fun w => H τ ((N : ℂ) * w - p)) := by
    exact (differentiable_H τ).comp (by fun_prop)
  have hD : Differentiable ℂ (fun w => ThetaWeierstrass.dividedTheta τ ((N : ℂ) * w)) := by
    exact (ThetaWeierstrass.differentiable_dividedTheta τ).comp (by fun_prop)
  have hiH : HasDerivAt (fun w : ℂ => (N : ℂ) * w - p) (N : ℂ) z := by
    simpa using! ((hasDerivAt_id z).const_mul (N : ℂ)).sub_const p
  have hiA : HasDerivAt (fun w : ℂ => (N : ℂ) * w) (N : ℂ) z := by
    simpa using! (hasDerivAt_id z).const_mul (N : ℂ)
  have hlogH : logDeriv (fun w : ℂ => H τ ((N : ℂ) * w - p)) z =
      logDeriv (H τ) ((N : ℂ) * z - p) * (N : ℂ) := by
    simpa only [Function.comp_def, hiH.deriv] using! logDeriv_comp
      (f := H τ) (g := fun w : ℂ => (N : ℂ) * w - p) (differentiable_H τ _) hiH.differentiableAt
  have hlogA : logDeriv (fun w : ℂ => ThetaWeierstrass.dividedTheta τ ((N : ℂ) * w)) z =
      ThetaWeierstrass.unitLogDerivative (H τ) 0 ((N : ℂ) * z) * (N : ℂ) := by
    simpa only [Function.comp_def, hiA.deriv, ThetaWeierstrass.unitLogDerivative, ThetaWeierstrass.dividedTheta,
      ThetaWeierstrass.logDerivative, logDeriv, Pi.div_apply] using!
      logDeriv_comp (f := ThetaWeierstrass.dividedTheta τ) (g := fun w : ℂ => (N : ℂ) * w)
        (ThetaWeierstrass.differentiable_dividedTheta τ _) hiA.differentiableAt
  unfold kernelUnit
  rw [logDeriv_fun_div (f := TorsionFourierComparison.kernelNumerator N a b τ)
    (g := unitDenominator N τ) z
    (by rw [hn]; exact mul_ne_zero hC (mul_ne_zero (Complex.exp_ne_zero _) hp))
    (by change (N : ℂ) * ThetaWeierstrass.dividedTheta τ ((N : ℂ) * z) ≠ 0; exact mul_ne_zero hN hA)
    (TorsionFourierComparison.differentiable_kernelNumerator N a b τ z)
    (differentiable_unitDenominator N τ z), hn]
  change logDeriv (fun w : ℂ => C * (cexp (scale * (a : ℂ) * w) * H τ ((N : ℂ) * w - p))) z -
    logDeriv (fun w : ℂ => (N : ℂ) * ThetaWeierstrass.dividedTheta τ ((N : ℂ) * w)) z = _
  rw [logDeriv_const_mul z C hC,
    logDeriv_fun_mul (f := fun w : ℂ => cexp (scale * (a : ℂ) * w))
      (g := fun w : ℂ => H τ ((N : ℂ) * w - p)) z (Complex.exp_ne_zero _) hp (by fun_prop) (hH z),
    logDeriv_const_mul z (N : ℂ) hN, he, hlogH, hlogA]
  dsimp only [p]
  ring

theorem kernelUnit_log_germ (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    logDeriv (kernelUnit N a b τ) =ᶠ[𝓝 (0 : ℂ)] (fun z => scale * (a : ℂ) +
      (N : ℂ) * logDeriv (H τ) ((N : ℂ) * z - torsionPoint N a b τ) -
      (N : ℂ) * ThetaWeierstrass.unitLogDerivative (H τ) 0 ((N : ℂ) * z)) := by
  have hp : ContinuousAt (fun z : ℂ => H τ ((N : ℂ) * z - torsionPoint N a b τ)) 0 := by
    exact ((differentiable_H τ).continuous.comp (by fun_prop)).continuousAt
  have ha : ContinuousAt (fun z : ℂ => ThetaWeierstrass.dividedTheta τ ((N : ℂ) * z)) 0 := by
    exact ((ThetaWeierstrass.differentiable_dividedTheta τ).continuous.comp (by fun_prop)).continuousAt
  filter_upwards [hp.eventually_ne (by simpa using TorsionFourierKernel.H_minus_torsion_ne N a b τ hg),
    ha.eventually_ne (by simpa using ThetaWeierstrass.dividedTheta_zero_ne_zero τ)] with z hz ha
  exact kernelUnit_log N a b τ hg z hz ha

theorem kernelUnit_log_jets (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    logDeriv (kernelUnit N a b τ) 0 = (N : ℂ) * lambdaValue N a b τ ∧
    deriv (logDeriv (kernelUnit N a b τ)) 0 = -(N : ℂ) ^ 2 * xValue N a b τ ∧
    iteratedDeriv 2 (logDeriv (kernelUnit N a b τ)) 0 = (N : ℂ) ^ 3 * yValue N a b τ := by
  let p := torsionPoint N a b τ
  let U := ThetaWeierstrass.unitLogDerivative (H τ) 0
  have hHp := TorsionFourierKernel.H_minus_torsion_ne N a b τ hg
  have hL : AnalyticAt ℂ (logDeriv (H τ)) (-p) :=
    ((differentiable_H τ).analyticAt (-p)).deriv.div ((differentiable_H τ).analyticAt (-p)) hHp
  have hU := ThetaWeierstrass.analyticAt_unitLogDerivative_zero τ
  have heq := kernelUnit_log_germ N a b τ hg
  have h0 := heq.eq_of_nhds
  have hd := heq.deriv_eq
  have hdd := heq.iteratedDeriv_eq 2
  have hl1 : deriv (fun z : ℂ => logDeriv (H τ) ((N : ℂ) * z - p)) 0 =
      (N : ℂ) * deriv (logDeriv (H τ)) (-p) := by
    simpa only [sub_eq_add_neg, mul_zero, zero_add] using deriv_affine (N : ℂ) (-p) 0 (by simpa using hL)
  have hu1 : deriv (fun z : ℂ => U ((N : ℂ) * z)) 0 = (N : ℂ) * ThetaWeierstrass.finitePart τ := by
    simpa only [add_zero, mul_zero, ThetaWeierstrass.finitePart, U] using deriv_affine (N : ℂ) 0 0
      (by simpa only [mul_zero, zero_add] using hU)
  have hl2 : iteratedDeriv 2 (fun z : ℂ => logDeriv (H τ) ((N : ℂ) * z - p)) 0 =
      (N : ℂ) ^ 2 * iteratedDeriv 2 (logDeriv (H τ)) (-p) := by
    simpa only [sub_eq_add_neg] using second_affine (N : ℂ) (-p) hL
  have hu2 : iteratedDeriv 2 (fun z : ℂ => U ((N : ℂ) * z)) 0 = 0 := by
    have h := second_affine (N : ℂ) 0 hU
    simpa only [add_zero, unitLog_second_zero, mul_zero] using h
  have hL0 : AnalyticAt ℂ (logDeriv (H τ)) ((N : ℂ) * 0 - p) := by simpa only [mul_zero, zero_sub] using hL
  have hU0 : AnalyticAt ℂ U ((N : ℂ) * 0) := by simpa only [mul_zero] using hU
  have hA : AnalyticAt ℂ (fun z : ℂ => logDeriv (H τ) ((N : ℂ) * z - p)) 0 :=
    hL0.comp (f := fun z : ℂ => (N : ℂ) * z - p) (x := (0 : ℂ)) (by fun_prop)
  have hB : AnalyticAt ℂ (fun z : ℂ => U ((N : ℂ) * z)) 0 :=
    hU0.comp (f := fun z : ℂ => (N : ℂ) * z) (x := (0 : ℂ)) (by fun_prop)
  have hScaledA : AnalyticAt ℂ (fun z : ℂ => scale * (a : ℂ) +
      (N : ℂ) * logDeriv (H τ) ((N : ℂ) * z - p)) 0 :=
    analyticAt_const.add (analyticAt_const.mul hA)
  have hScaledB : AnalyticAt ℂ (fun z : ℂ => (N : ℂ) * U ((N : ℂ) * z)) 0 :=
    analyticAt_const.mul hB
  have hwp := ThetaWeierstrass.weierstrassP_eq_neg_deriv_logDerivative τ (-p)
    (fun h => hHp ((ThetaWeierstrass.H_zero_iff_mem_lattice τ (-p)).mpr h))
  have hxp : (ThetaWeierstrass.periodPair τ).weierstrassP (-p) = xValue N a b τ := by
    rw [PeriodPair.weierstrassP_neg, xValue_of_good N a b τ hg]
  have hyp : (ThetaWeierstrass.periodPair τ).derivWeierstrassP (-p) = -yValue N a b τ := by
    rw [PeriodPair.derivWeierstrassP_neg, yValue_of_good N a b τ hg]
  have hwp2 := wp_deriv_eq_neg_log_second τ hHp
  constructor
  · rw [h0]
    simp only [mul_zero, zero_sub, ThetaWeierstrass.unitLogDerivative_zero, mul_zero, sub_zero,
      H_log_neg, lambdaValue_eq_log N a b τ hg]
    change scale * (a : ℂ) + (N : ℂ) * (-logDeriv (H τ) p) =
      (N : ℂ) * (scale * (a : ℂ) / N - logDeriv (H τ) p)
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne N)]
    ring
  · constructor
    · rw [hd]
      change deriv (fun z : ℂ => scale * (a : ℂ) + (N : ℂ) * logDeriv (H τ) ((N : ℂ) * z - p) -
        (N : ℂ) * U ((N : ℂ) * z)) 0 = _
      rw [deriv_fun_sub hScaledA.differentiableAt hScaledB.differentiableAt, deriv_const_add,
        deriv_const_mul_field, deriv_const_mul_field, hl1, hu1]
      rw [hxp] at hwp
      change xValue N a b τ = -deriv (logDeriv (H τ)) (-p) + ThetaWeierstrass.finitePart τ at hwp
      linear_combination (N : ℂ) ^ 2 * hwp
    · rw [hdd]
      change iteratedDeriv 2 (fun z : ℂ => scale * (a : ℂ) + (N : ℂ) * logDeriv (H τ) ((N : ℂ) * z - p) -
        (N : ℂ) * U ((N : ℂ) * z)) 0 = _
      rw [iteratedDeriv_fun_sub hScaledA.contDiffAt hScaledB.contDiffAt,
        iteratedDeriv_const_add (by decide),
        iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, hl2, hu2]
      rw [hyp] at hwp2
      change -yValue N a b τ = -iteratedDeriv 2 (logDeriv (H τ)) (-p) at hwp2
      linear_combination (N : ℂ) ^ 3 * hwp2

/-- The third derivative of the actual analytic unit, derived from its three logarithmic jets. -/
theorem kernelUnit_third_zero (N : ℕ) [NeZero N] (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    iteratedDeriv 3 (kernelUnit N a b τ) 0 =
      (N : ℂ) ^ 2 * (cubicValue N a b τ + yValue N a b τ) := by
  have h := analytic_third_jet (analyticAt_kernelUnit N a b τ)
    (by rw [kernelUnit_zero N a b τ hg]; exact inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N)))
  obtain ⟨h0, h1, h2⟩ := kernelUnit_log_jets N a b τ hg
  rw [kernelUnit_zero N a b τ hg, h0, h1, h2] at h
  rw [h]
  unfold cubicValue
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne N)]
  ring

end ZInQ.Contrib.HeckePrimeRationality.TorsionWeightThree
