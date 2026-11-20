import ZInQKernel.Contrib.OneProof.RC.CMField2.ExactOrderProof
import ZInQKernel.Contrib.OneProof.RC.CMField2.OrientedIdeals

/-! The degree bound for a singular modulus specified by a primitive period
equation. The statement uses the analytic inputs of the fork's
`ZInQKernel/Contrib/OneProof/CMjBridgesPrint.lean` at
`dfc6804f30bb08ec33abefeca76cba33405b8984`; its equality is not used. -/

open NumberField TauCeti.GlobalNumberFields ZInQ.Contrib.CloudB3RC53.CST
open scoped UpperHalfPlane

namespace ZInQ.Manuscript.RC.CMField2

/-- The root in the upper half-plane of a quadratic equation with positive
leading coefficient is the parameter for its form. -/
theorem eq_cmPoint_of_quadratic {τ : ℍ} {A B C d : ℤ} (hA : 0 < A)
    (hΔ : B ^ 2 - 4 * A * C = d)
    (hroot : (A : ℂ) * (τ : ℂ)^2 + (B : ℂ) * (τ : ℂ) + (C : ℂ) = 0) :
    d < 0 ∧ τ = cmPoint A B d := by
  let z := (τ : ℂ)
  have ha : (0 : ℝ) < A := by exact_mod_cast hA
  have hΔR : (B : ℝ)^2 - 4 * (A : ℝ) * (C : ℝ) = (d : ℝ) := by exact_mod_cast hΔ
  have hr := congrArg Complex.re hroot
  have hi := congrArg Complex.im hroot
  simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero, sub_zero,
    Complex.zero_re, Complex.zero_im] at hr hi
  have hz : z.im * (2 * (A : ℝ) * z.re + (B : ℝ)) = 0 := by linear_combination hi
  have hx := (mul_eq_zero.mp hz).resolve_left τ.im_pos.ne'
  have hs : (2 * (A : ℝ) * z.im)^2 = -(d : ℝ) := by
    linear_combination -4 * (A : ℝ) * hr + congrArg (fun x : ℝ => x ^ 2) hx - hΔR
  have hp : 0 < 2 * (A : ℝ) * z.im := by exact mul_pos (mul_pos (by norm_num) ha) τ.im_pos
  have hd : d < 0 := by
    have hdR : (d : ℝ) < 0 := by linarith [sq_pos_of_ne_zero hp.ne']
    exact_mod_cast hdR
  have hy : 2 * (A : ℝ) * z.im = Real.sqrt (-(d : ℝ)) := by
    apply (sq_eq_sq₀ hp.le (Real.sqrt_nonneg _)).mp
    rwa [Real.sq_sqrt (by exact_mod_cast neg_nonneg.mpr hd.le)]
  refine ⟨hd, UpperHalfPlane.coe_injective ?_⟩
  change z = (cmPoint A B d : ℂ)
  rw [coe_cmPoint_of_neg hA hd, show (2 : ℂ) * (A : ℂ) = ((2 * (A : ℝ) : ℝ) : ℂ) by norm_cast]
  apply Complex.ext
  · rw [Complex.div_ofReal_re]
    simp [Complex.mul_re]
    exact (eq_div_iff (by positivity : 2 * (A : ℝ) ≠ 0)).mpr (by linarith)
  · rw [Complex.div_ofReal_im]
    simp [Complex.mul_im]
    exact (eq_div_iff (by positivity : 2 * (A : ℝ) ≠ 0)).mpr (by linarith)

/-- The degree bound in terms of the analytic primitive equation, over ℚ.
This is the upper-bound direction of the fork's degree print, with the class
number expressed as the number of elements of the Picard group. -/
theorem singularModulus_finrank_le_of_primitive_equation
    {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)
    (hk : Module.finrank ℚ K = 2) (hc : IsTotallyComplex K)
    {τ : ℍ} {A B C d : ℤ} (hD : O.discr = d) (hA : 0 < A)
    (hΔ : B ^ 2 - 4 * A * C = d) (hprim : Int.gcd (Int.gcd A B : ℤ) C = 1)
    (hroot : (A : ℂ) * (τ : ℂ)^2 + (B : ℂ) * (τ : ℂ) + (C : ℂ) = 0) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {X0Model.analyticJ τ}) ≤ Nat.card (Pic O) := by
  obtain ⟨hd, rfl⟩ := eq_cmPoint_of_quadratic hA hΔ hroot
  have hf : IsHeegnerForm 1 d A B C := ⟨hA, one_dvd A, hΔ, hprim⟩
  obtain ⟨κ, I, _, hI, _⟩ := exists_heegner_singularModuli O hk hc hD hd isCoprime_one_right hf
  rw [hI]
  exact singularModulus_finrank_le O hk hc κ I


end ZInQ.Manuscript.RC.CMField2
