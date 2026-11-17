import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionWeierstrassData
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionFourierComparison
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The second Laurent coefficient of the actual torsion kernel

The analytic unit of the theta quotient is constructed by removing the simple
origin zero from the denominator. Its second derivative is computed from actual
theta derivatives and the actual Weierstrass normalization. No Laurent or finite
Fourier identity is an assumption.
-/

noncomputable section
set_option autoImplicit false
open Complex UpperHalfPlane Filter
open scoped Topology

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionMuFourierKernel

open CompletedTheta TorsionFourierKernel TorsionFourierComparison
open TorsionWeierstrassData

variable (N : ℕ) [NeZero N]

/-- The denominator after removing its simple zero at the origin. -/
def unitDenominator (τ : ℍ) (z : ℂ) : ℂ :=
  (N : ℂ) * ThetaWeierstrass.dividedTheta τ ((N : ℂ) * z)

/-- The analytic unit whose punctured values are z times the actual kernel. -/
def kernelUnit (a b : ℤ) (τ : ℍ) (z : ℂ) : ℂ :=
  kernelNumerator N a b τ z / unitDenominator N τ z

lemma unitDenominator_zero (τ : ℍ) : unitDenominator N τ 0 = (N : ℂ) * Hder τ 0 := by
  simp only [unitDenominator, mul_zero, ThetaWeierstrass.dividedTheta_zero, deriv_H]

lemma unitDenominator_zero_ne (τ : ℍ) : unitDenominator N τ 0 ≠ 0 := by
  rw [unitDenominator_zero]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N)) (Hder_zero_ne τ)

lemma differentiable_unitDenominator (τ : ℍ) : Differentiable ℂ (unitDenominator N τ) := by
  exact ((ThetaWeierstrass.differentiable_dividedTheta τ).comp (by fun_prop)).const_mul (N : ℂ)

lemma analyticAt_kernelUnit (a b : ℤ) (τ : ℍ) : AnalyticAt ℂ (kernelUnit N a b τ) 0 :=
  ((differentiable_kernelNumerator N a b τ).analyticAt 0).div
    ((differentiable_unitDenominator N τ).analyticAt 0) (unitDenominator_zero_ne N τ)

lemma kernelUnit_zero (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) : kernelUnit N a b τ 0 = (N : ℂ)⁻¹ := by
  have hden := H_minus_torsion_ne N a b τ hg
  have hH := Hder_zero_ne τ
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [kernelUnit, unitDenominator_zero]
  simp only [kernelNumerator, mul_zero, zero_sub, Complex.exp_zero, mul_one]
  field_simp [hden, hH, hN]

lemma dilated_factorization (τ : ℍ) (z : ℂ) :
    H τ ((N : ℂ) * z) = z * unitDenominator N τ z := by
  rw [ThetaWeierstrass.H_eq_mul_dividedTheta]
  simp only [unitDenominator]
  ring

/-- A genuine punctured-neighborhood identity with the actual kernel. -/
lemma kernelUnit_germ (a b : ℤ) (τ : ℍ) :
    (fun z : ℂ => z * kernel N a b τ z) =ᶠ[𝓝[≠] 0] kernelUnit N a b τ := by
  have hn := (differentiable_unitDenominator N τ 0).continuousAt.eventually_ne
    (unitDenominator_zero_ne N τ)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzne
  rw [kernel_eq_quotient, show dilated N τ z = z * unitDenominator N τ z from
    dilated_factorization N τ z]
  unfold kernelUnit
  have hz0 : z ≠ 0 := hzne
  field_simp [hz, hz0]

/-- The actual first derivative agrees with the established finite part. -/
lemma kernelUnit_deriv_zero (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    deriv (kernelUnit N a b τ) 0 = lambdaValue N a b τ := by
  have hd := (analyticAt_kernelUnit N a b τ).differentiableAt.hasDerivAt.tendsto_slope_zero
  have ht := kernel_finitePart_zero N a b τ hg
  have hE0 := kernelUnit_zero N a b τ hg
  have he : (fun z : ℂ => kernel N a b τ z - 1 / ((N : ℂ) * z)) =ᶠ[𝓝[≠] 0]
      (fun z => (kernelUnit N a b τ z - kernelUnit N a b τ 0) / z) := by
    filter_upwards [kernelUnit_germ N a b τ, self_mem_nhdsWithin] with z hz hzne
    rw [← hz, hE0]
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have hz0 : z ≠ 0 := hzne
    field_simp [hN, hz0]
  have hd' : Tendsto (fun z : ℂ => (kernelUnit N a b τ z - kernelUnit N a b τ 0) / z)
      (𝓝[≠] 0) (𝓝 (deriv (kernelUnit N a b τ) 0)) := by
    simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
  have hv := tendsto_nhds_unique (ht.congr' he) hd'
  simpa only [lambdaValue, scale, mul_assoc] using hv.symm

private lemma second_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    iteratedDeriv 2 (fun z => f z * g z) 0 =
      f 0 * iteratedDeriv 2 g 0 + 2 * deriv f 0 * deriv g 0 + iteratedDeriv 2 f 0 * g 0 := by
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt]
  simp only [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one]
  norm_num

lemma unitDenominator_deriv_zero (τ : ℍ) : deriv (unitDenominator N τ) 0 = 0 := by
  have hm : HasDerivAt (fun z : ℂ => (N : ℂ) * z) (N : ℂ) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (N : ℂ)
  have hd := ((ThetaWeierstrass.differentiable_dividedTheta τ) ((N : ℂ) * 0)).hasDerivAt.comp 0 hm
  have he := hd.const_mul (N : ℂ)
  have hev := he.deriv
  change deriv (unitDenominator N τ) 0 = _ at hev
  simpa only [mul_zero, ThetaWeierstrass.deriv_dividedTheta_zero, zero_mul, mul_zero] using hev

lemma unitDenominator_second_zero (τ : ℍ) :
    iteratedDeriv 2 (unitDenominator N τ) 0 =
      (N : ℂ) ^ 3 * Hder τ 0 * ThetaWeierstrass.finitePart τ := by
  have hc := congrFun (iteratedDeriv_comp_const_mul
    (n := 2) (ThetaWeierstrass.differentiable_dividedTheta τ).contDiff (N : ℂ)) 0
  have hs : iteratedDeriv 2 (unitDenominator N τ) 0 =
      (N : ℂ) ^ 3 * iteratedDeriv 2 (ThetaWeierstrass.dividedTheta τ) 0 := by
    change iteratedDeriv 2 (fun z : ℂ => (N : ℂ) *
      ThetaWeierstrass.dividedTheta τ ((N : ℂ) * z)) 0 = _
    rw [iteratedDeriv_const_mul_field, hc]
    simp only [mul_zero]
    ring
  rw [hs, ThetaWeierstrass.finitePart_eq_second_unit_derivative,
    ThetaWeierstrass.dividedTheta_zero, deriv_H]
  have hn := Hder_zero_ne τ
  field_simp [hn]

private lemma deriv_exp_linear (s z : ℂ) :
    deriv (fun w : ℂ => Complex.exp (s * w)) z = Complex.exp (s * z) * s := by
  simpa using ((hasDerivAt_id z).const_mul s).cexp.deriv

private lemma second_exp_linear (s : ℂ) :
    iteratedDeriv 2 (fun z : ℂ => Complex.exp (s * z)) 0 = s ^ 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, funext (deriv_exp_linear s)]
  have hd := (((hasDerivAt_id (0 : ℂ)).const_mul s).cexp).mul_const s
  simpa only [id_eq, mul_zero, Complex.exp_zero, one_mul, mul_one, sq] using hd.deriv

private lemma H_second_neg (τ : ℍ) (z : ℂ) :
    iteratedDeriv 2 (H τ) (-z) = -iteratedDeriv 2 (H τ) z := by
  have he : (fun w : ℂ => Hder τ (-w)) = Hder τ := funext (Hder_neg τ)
  have hd := deriv_comp_neg (Hder τ) z
  rw [he] at hd
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, funext (deriv_H τ)]
  linear_combination hd

private lemma log_deriv_ratio (τ : ℍ) (z : ℂ) (hz : H τ z ≠ 0) :
    deriv (ThetaWeierstrass.logDerivative (H τ)) z =
      iteratedDeriv 2 (H τ) z / H τ z - (Hder τ z / H τ z) ^ 2 := by
  have hd := (((differentiable_H τ).analyticAt z).deriv.differentiableAt.hasDerivAt).div
    ((differentiable_H τ) z).hasDerivAt hz
  change deriv (deriv (H τ) / H τ) z = _
  rw [hd.deriv]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv_H]
  field_simp [hz]

lemma lambdaValue_eq_log (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    lambdaValue N a b τ = scale * (a : ℂ) / (N : ℂ) -
      ThetaWeierstrass.logDerivative (H τ) (torsionPoint N a b τ) := by
  rw [lambdaValue, reg_eq_logDerivative N a b τ hg]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  unfold scale
  field_simp [hN, hpi]
  ring

lemma kernelNumerator_second_zero (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    iteratedDeriv 2 (kernelNumerator N a b τ) 0 =
      Hder τ 0 * (N : ℂ) ^ 2 *
        (lambdaValue N a b τ ^ 2 + ThetaWeierstrass.finitePart τ - xValue N a b τ) := by
  let u := torsionPoint N a b τ
  let s : ℂ := scale * (a : ℂ)
  have hu := H_torsion_ne_zero N (NeZero.pos N) τ a b hg
  have hu0 : H τ u ≠ 0 := hu
  have hun := H_minus_torsion_ne N a b τ hg
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hshift : ContDiff ℂ 2 (fun z : ℂ => H τ (z - u)) := by
    exact (differentiable_H τ).contDiff.comp (by fun_prop)
  have hs2 := congrFun (iteratedDeriv_comp_const_mul (n := 2) hshift (N : ℂ)) 0
  rw [iteratedDeriv_comp_sub_const] at hs2
  have hn2 : iteratedDeriv 2 (fun z : ℂ => H τ ((N : ℂ) * z - u)) 0 =
      (N : ℂ) ^ 2 * iteratedDeriv 2 (H τ) (-u) := by
    simpa only [mul_zero, zero_sub] using hs2
  have hn1 : deriv (fun z : ℂ => H τ ((N : ℂ) * z - u)) 0 = Hder τ (-u) * (N : ℂ) := by
    have hm := ((hasDerivAt_id (0 : ℂ)).const_mul (N : ℂ)).sub_const u
    simpa only [Function.comp_def, id_eq, mul_zero, zero_sub, mul_one] using
      ((hasDerivAt_H τ ((N : ℂ) * 0 - u)).comp 0 hm).deriv
  have he : kernelNumerator N a b τ = fun z : ℂ =>
      Hder τ 0 / H τ (-u) * (Complex.exp (s * z) * H τ ((N : ℂ) * z - u)) := by
    funext z
    simp only [kernelNumerator, s, scale, u]
    ring
  have hna : AnalyticAt ℂ (fun z : ℂ => H τ ((N : ℂ) * z - u)) 0 :=
    ((differentiable_H τ).comp (by fun_prop : Differentiable ℂ
      (fun z : ℂ => (N : ℂ) * z - u))).analyticAt 0
  rw [he, iteratedDeriv_const_mul_field]
  rw [second_mul (by fun_prop) hna]
  rw [second_exp_linear, hn1, hn2, deriv_exp_linear]
  simp only [mul_zero, zero_sub, Complex.exp_zero, one_mul]
  rw [Hder_neg, H_second_neg, H_neg]
  have hx := ThetaWeierstrass.weierstrassP_eq_neg_deriv_logDerivative τ u
    (fun hz => hu ((ThetaWeierstrass.H_zero_iff_mem_lattice τ u).mpr hz))
  change (ThetaWeierstrass.periodPair τ).weierstrassP u =
    -deriv (ThetaWeierstrass.logDerivative (H τ)) u + ThetaWeierstrass.finitePart τ at hx
  rw [log_deriv_ratio τ u hu] at hx
  rw [xValue_of_good N a b τ hg, lambdaValue_eq_log N a b τ hg]
  simp only [ThetaWeierstrass.logDerivative, deriv_H]
  change _ = Hder τ 0 * (N : ℂ) ^ 2 *
    ((s / (N : ℂ) - Hder τ u / H τ u) ^ 2 + ThetaWeierstrass.finitePart τ -
      (ThetaWeierstrass.periodPair τ).weierstrassP u)
  rw [hx]
  field_simp [hu0, hN]
  ring

/-- The second derivative of the genuine analytic kernel unit equals 2Nμ. -/
theorem kernelUnit_second_zero (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    iteratedDeriv 2 (kernelUnit N a b τ) 0 = 2 * (N : ℂ) * muValue N a b τ := by
  have hn := (differentiable_unitDenominator N τ 0).continuousAt.eventually_ne
    (unitDenominator_zero_ne N τ)
  have he : (fun z => kernelUnit N a b τ z * unitDenominator N τ z) =ᶠ[𝓝 0]
      kernelNumerator N a b τ := by
    filter_upwards [hn] with z hz
    exact div_mul_cancel₀ _ hz
  have hd := he.iteratedDeriv_eq 2
  rw [second_mul (analyticAt_kernelUnit N a b τ)
    ((differentiable_unitDenominator N τ).analyticAt 0),
    unitDenominator_deriv_zero, unitDenominator_second_zero, unitDenominator_zero,
    kernelUnit_zero N a b τ hg, kernelNumerator_second_zero N a b τ hg] at hd
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hH := Hder_zero_ne τ
  field_simp [hN] at hd
  have hv : iteratedDeriv 2 (kernelUnit N a b τ) 0 =
      (N : ℂ) * (lambdaValue N a b τ ^ 2 - xValue N a b τ) := by
    apply mul_right_cancel₀ (mul_ne_zero hN hH)
    linear_combination hd
  rw [hv]
  unfold muValue
  ring

end ZInQ.Contrib.HeckePrimeRationality.TorsionMuFourierKernel
