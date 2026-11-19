import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Local
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Real Fresnel normalization for the positive additive character
(tex 8651–8653, 8746–8753). The Gaussian regularization is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.WeilIndex

open Visibility Filter
open scoped Topology Real

private theorem zetaEight_sq_complex : (zetaEight : ℂ) ^ 2 = Complex.I := by
  change Complex.exp (↑π / 4 * Complex.I) ^ 2 = _
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_pi_div_two_mul_I using 2; ring

private theorem zetaEight_re (negative : Bool) :
    0 < (↑(if negative then zetaEight⁻¹ else zetaEight) : ℂ).re := by
  cases negative
  · change 0 < (Complex.exp (↑π / 4 * Complex.I)).re
    rw [Complex.exp_re]
    simp [Complex.mul_re, Complex.mul_im,
      Real.cos_pi_div_four, Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]
  · change 0 < ((zetaEight⁻¹ : ℂˣ) : ℂ).re
    rw [Units.val_inv_eq_inv_val]
    change 0 < (Complex.exp (↑π / 4 * Complex.I))⁻¹.re
    rw [← Complex.exp_neg, Complex.exp_re]
    simp [Complex.mul_re, Complex.mul_im,
      Real.cos_pi_div_four, Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]

/-- Coefficient of the quadratic exponent with positive real damping. -/
def gaussianParameter (a ε : ℝ) : ℂ := ε - 2 * π * Complex.I * (a : ℂ)

private theorem gaussianParameter_re (a ε : ℝ) : (gaussianParameter a ε).re = ε := by
  simp [gaussianParameter, Complex.mul_re, Complex.mul_im]

private theorem gaussianParameter_zero (a : ℝˣ) :
    gaussianParameter a 0 = -(2 * π * Complex.I * (a : ℂ)) := by simp [gaussianParameter]

private theorem pi_div_parameter (a : ℝˣ) :
    (π : ℂ) / gaussianParameter a 0 = Complex.I / (2 * (a : ℂ)) := by
  have ha : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr a.ne_zero
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [gaussianParameter_zero]
  field_simp
  exact Complex.I_sq.symm

private theorem real_gamma_sq (a : ℝˣ) :
    (gammaReal a : ℂ) ^ 2 = if 0 < (a : ℝ) then Complex.I else -Complex.I := by
  by_cases ha : 0 < (a : ℝ)
  · rw [gammaReal_pos ha, ite_eq_left ha, zetaEight_sq_complex]
  · rw [gammaReal_neg (lt_of_le_of_ne (le_of_not_gt ha) a.ne_zero), ite_eq_right ha,
      Units.val_inv_eq_inv_val, inv_pow, zetaEight_sq_complex, Complex.inv_I]

private theorem pi_div_parameter_sqrt (a : ℝˣ) :
    (Real.sqrt |2 * (a : ℝ)| : ℂ) * ((π : ℂ) / gaussianParameter a 0) ^ (1 / 2 : ℂ) =
      (gammaReal a : ℂ) := by
  let r := Real.sqrt |2 * (a : ℝ)|
  have hr : 0 < r := Real.sqrt_pos.mpr (abs_pos.mpr (mul_ne_zero (by norm_num) a.ne_zero))
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hr2 : (r : ℂ) ^ 2 = ((|2 * (a : ℝ)| : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (abs_nonneg (2 * (a : ℝ)))
  have hs : (π : ℂ) / gaussianParameter a 0 = ((gammaReal a : ℂ) / (r : ℂ)) ^ 2 := by
    rw [pi_div_parameter, div_pow, real_gamma_sq, hr2]
    by_cases ha : 0 < (a : ℝ)
    · rw [ite_eq_left ha, abs_of_pos (mul_pos (by norm_num) ha)]
      push_cast
      rfl
    · rw [ite_eq_right ha, abs_of_neg (mul_neg_of_pos_of_neg (by norm_num)
        (lt_of_le_of_ne (le_of_not_gt ha) a.ne_zero)), Complex.ofReal_neg, neg_div_neg_eq]
      push_cast
      rfl
  have hpos : 0 < ((gammaReal a : ℂ) / (r : ℂ)).re := by
    rw [Complex.div_ofReal_re]
    apply div_pos _ hr
    by_cases ha : 0 < (a : ℝ)
    · rw [gammaReal_pos ha]; exact zetaEight_re false
    · rw [gammaReal_neg (lt_of_le_of_ne (le_of_not_gt ha) a.ne_zero)]; exact zetaEight_re true
  change (r : ℂ) * _ = _
  rw [hs, show (1 / 2 : ℂ) = 2⁻¹ by simp, Complex.sq_cpow_two_inv hpos]
  field_simp

/-- With the positive real additive character and polar Haar measure, the
Gaussian regularization of the one-dimensional integral is exactly the
existing real index. -/
theorem real_normalized_gauss_limit (a : ℝˣ) :
    Tendsto (fun ε : ℝ => (Real.sqrt |2 * (a : ℝ)| : ℂ) *
      ∫ x : ℝ, Complex.exp (-gaussianParameter a ε * (x : ℂ) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (gammaReal a : ℂ)) := by
  have hb : gaussianParameter a 0 ≠ 0 := by
    rw [gaussianParameter_zero]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero
      (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr a.ne_zero))
  have hcont : ContinuousAt (fun ε : ℝ => (π : ℂ) / gaussianParameter a ε) 0 := by
    apply continuousAt_const.div _ hb
    unfold gaussianParameter
    fun_prop
  have hslit : (π : ℂ) / gaussianParameter a 0 ∈ Complex.slitPlane := by
    rw [pi_div_parameter, show (2 * (a : ℂ)) = ((2 * (a : ℝ) : ℝ) : ℂ) by push_cast; rfl]
    apply Or.inr
    rw [Complex.div_ofReal_im, Complex.I_im]
    exact div_ne_zero one_ne_zero (mul_ne_zero two_ne_zero a.ne_zero)
  have hlim : ContinuousAt (fun ε : ℝ => ((π : ℂ) / gaussianParameter a ε) ^ (1 / 2 : ℂ)) 0 :=
    (continuousAt_cpow_const hslit).tendsto.comp hcont.tendsto
  have hlim' : Tendsto (fun ε : ℝ => (Real.sqrt |2 * (a : ℝ)| : ℂ) *
        ((π : ℂ) / gaussianParameter a ε) ^ (1 / 2 : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (gammaReal a : ℂ)) := by
    rw [← pi_div_parameter_sqrt a]
    exact tendsto_const_nhds.mul (hlim.tendsto.mono_left nhdsWithin_le_nhds)
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < (gaussianParameter a ε).re := by
    rw [gaussianParameter_re]; exact hε
  rw [integral_gaussian_complex hε']

#print axioms zetaEight_sq_complex
#print axioms zetaEight_re
#print axioms gaussianParameter_re
#print axioms gaussianParameter_zero
#print axioms pi_div_parameter
#print axioms real_gamma_sq
#print axioms pi_div_parameter_sqrt
#print axioms real_normalized_gauss_limit

end ZInQ.Manuscript.RC.WeilIndex
