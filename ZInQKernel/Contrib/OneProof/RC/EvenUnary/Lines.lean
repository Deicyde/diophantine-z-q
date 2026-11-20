import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Coset

/-! The derivative of the two-variable Jacobi equation gives Poisson
summation with one linear factor (tex 9620–9623). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenUnary

open Complex
open scoped Real

/-- A Gaussian twisted by the additive frequency `u`, with its linear weight. -/
def linearTheta (u τ : ℂ) : ℂ :=
  ∑' n : ℤ, (n : ℂ) * jacobiTheta₂_term n u τ

/-- A Gaussian on an offset line, with the linear weight at the offset point. -/
def linearLine (r τ : ℂ) : ℂ :=
  ∑' n : ℤ, ((n : ℂ) + r) * exp (π * I * τ * ((n : ℂ) + r) ^ 2)

private theorem jacobiDerivative_ne : (2 * (π : ℂ) * I) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero

theorem linearTheta_hasSum (u : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => (n : ℂ) * jacobiTheta₂_term n u τ) (linearTheta u τ) := by
  have h := (hasSum_jacobiTheta₂'_term u hτ).summable.mul_left (2 * (π : ℂ) * I)⁻¹
  apply Summable.hasSum
  convert h using 1
  ext n
  rw [jacobiTheta₂'_term, mul_assoc (2 * (π : ℂ) * I), inv_mul_cancel_left₀ jacobiDerivative_ne]

private theorem jacobiDerivative_eq (u τ : ℂ) :
    jacobiTheta₂' u τ = (2 * (π : ℂ) * I) * linearTheta u τ := by
  rw [jacobiTheta₂', linearTheta, ← tsum_mul_left]
  exact tsum_congr fun n => by rw [jacobiTheta₂'_term, mul_assoc]

theorem linearLine_hasSum (r : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => ((n : ℂ) + r) * exp (π * I * τ * ((n : ℂ) + r) ^ 2))
      (linearLine r τ) := by
  let f := (linearTheta_hasSum (r * τ) hτ).summable.add
    ((hasSum_jacobiTheta₂_term (r * τ) hτ).summable.mul_left r)
  apply Summable.hasSum
  convert f.mul_left (exp (π * I * τ * r ^ 2)) using 1
  ext n
  simp only [← add_mul, mul_left_comm (exp _), jacobiTheta₂_term, ← exp_add]
  congr 2
  ring

private theorem linearLine_eq (r : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    linearLine r τ =
      exp (π * I * τ * r ^ 2) * (linearTheta (r * τ) τ + r * jacobiTheta₂ (r * τ) τ) := by
  apply (linearLine_hasSum r hτ).unique
  convert (((linearTheta_hasSum (r * τ) hτ).add
    ((hasSum_jacobiTheta₂_term (r * τ) hτ).mul_left r)).mul_left
      (exp (π * I * τ * r ^ 2))) using 1
  ext n
  simp only [← add_mul, mul_left_comm (exp _), jacobiTheta₂_term, ← exp_add]
  congr 2
  ring

/-- Weighted Poisson summation for an offset line. The derivative contributes
`1/τ` in addition to the unweighted Gaussian factor. The shift term in
the derivative of the exponential cancels the offset in the linear weight. -/
theorem linearLine_poisson (r : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    linearLine r τ = (1 / (-I * τ) ^ (1 / 2 : ℂ)) / τ * linearTheta r (-1 / τ) := by
  have hn : τ ≠ 0 := fun h => by simp [h] at hτ
  have hd := jacobiTheta₂'_functional_equation (r * τ) τ
  rw [jacobiDerivative_eq, jacobiDerivative_eq, mul_div_cancel_right₀ r hn] at hd
  have he : -(π : ℂ) * I * (r * τ) ^ 2 / τ = -(π * I * τ * r ^ 2) := by
    field_simp
  rw [he] at hd
  have hL : linearTheta (r * τ) τ =
      1 / (-I * τ) ^ (1 / 2 : ℂ) * exp (-(π * I * τ * r ^ 2)) / τ *
        (linearTheta r (-1 / τ) - (r * τ) * jacobiTheta₂ r (-1 / τ)) := by
    apply (mul_left_cancel₀ jacobiDerivative_ne)
    linear_combination hd
  rw [linearLine_eq r hτ, hL]
  rw [jacobiTheta₂_functional_equation (r * τ) τ, he, mul_div_cancel_right₀ r hn]
  have hc : exp (π * I * τ * r ^ 2) * exp (-(π * I * τ * r ^ 2)) = 1 := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  simp only [div_eq_mul_inv, one_mul]
  calc
    _ = (exp (π * I * τ * r ^ 2) * exp (-(π * I * τ * r ^ 2))) *
        ((-I * τ) ^ (1 / 2 : ℂ))⁻¹ *
        (τ⁻¹ * linearTheta r (-1 / τ) +
          r * (1 - τ * τ⁻¹) * jacobiTheta₂ r (-1 / τ)) := by ring
    _ = _ := by rw [hc, mul_inv_cancel₀ hn]; ring

/-- Integral translation on the Jacobi parameter retains the same linear
weight. For `τ = 2jz` this is the period-one transformation at a shell. -/
theorem linearTheta_periodic (u : ℂ) : Function.Periodic (linearTheta u) 2 := by
  intro τ
  have h := jacobiTheta₂'_add_right u τ
  rw [jacobiDerivative_eq, jacobiDerivative_eq] at h
  exact mul_left_cancel₀ jacobiDerivative_ne h

end ZInQ.Manuscript.RC.EvenUnary
