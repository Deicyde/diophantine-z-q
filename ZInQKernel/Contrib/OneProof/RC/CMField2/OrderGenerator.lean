import ZInQKernel.Contrib.OneProof.RC.CMField2.Integrality
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Orders.Discriminant

/-! The generator of an abstract quadratic order with its prescribed complex
image. On-the-spot calculation (c). -/

noncomputable section
open NumberField Module TauCeti.GlobalNumberFields Complex
open scoped nonZeroDivisors

namespace ZInQ.Manuscript.RC.CMField2

variable {K : Type} [Field K] [NumberField K]

/-- With 1 as the first order basis vector, the discriminant is the
discriminant of the monic quadratic equation of the other vector. -/
theorem discr_of_basis_one (O : NumberFieldOrder K)
    (b : Basis (Fin 2) ℤ O.toSubalgebra) (hb : b 0 = 1) :
    ∃ t u : ℤ,
      ((b 1 : K) ^ 2 - (t : K) * (b 1 : K) + (u : K) = 0) ∧
      O.discr = t ^ 2 - 4 * u := by
  let R := O.toSubalgebra
  let w : R := b 1
  let l := b.repr (w * w) 0
  let t := b.repr (w * w) 1
  have hw : w * w = l • (1 : R) + t • w := by
    have h := b.sum_repr (w * w)
    rw [Fin.sum_univ_two, hb] at h
    exact h.symm
  have h1 : Algebra.trace ℤ R 1 = 2 := by
    rw [Algebra.trace_eq_matrix_trace b, map_one]
    simp
  have htrace : Algebra.trace ℤ R w = t := by
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, Fin.sum_univ_two]
    simp [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, hb, w, Basis.repr_self, t]
  have hwtrace : Algebra.trace ℤ R (w * w) = 2 * l + t ^ 2 := by
    rw [hw, map_add, map_zsmul, map_zsmul, h1, htrace]
    change l * 2 + t * t = _
    ring
  refine ⟨t, -l, ?_, ?_⟩
  · have h := congrArg R.val hw
    simp only [map_mul, map_add, map_one, zsmul_eq_mul] at h
    change (w : K) * (w : K) = (l : K) * 1 + (t : K) * (w : K) at h
    push_cast
    linear_combination h
  · have hmat : Algebra.traceMatrix ℤ b = !![2, t; t, 2 * l + t ^ 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb]
      · exact h1
      · exact htrace
      · exact htrace
      · exact hwtrace
    rw [← O.discr_eq_discr b, Algebra.discr_def, hmat, Matrix.det_fin_two_of]
    ring

/-- A middle coefficient of the order's discriminant gives an oriented
generator of that order in a suitable complex embedding. -/
theorem exists_heegner_generator (O : NumberFieldOrder K)
    (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    {A B C d : ℤ} (hD : O.discr = d) (hd : d < 0) (hform : B ^ 2 - 4 * A * C = d) :
    ∃ (κ : K →+* ℂ) (ω : K), ω ∈ O.toSubalgebra ∧
      (∀ x : O.toSubalgebra, ∃ u v : ℤ, (x : K) = (u : K) + (v : K) * ω) ∧
      (ω ^ 2 + (B : K) * ω + (A : K) * (C : K) = 0) ∧
      κ ω = (-(B : ℂ) + I * (Real.sqrt (-(d : ℝ)) : ℂ)) / 2 := by
  obtain ⟨b, hb⟩ := exists_order_basis_one O hk
  obtain ⟨t, u, hpoly, hdis⟩ := discr_of_basis_one O b hb
  have hdisc : t ^ 2 - 4 * u = d := hdis.symm.trans hD
  let κ₀ : K →+* ℂ := Classical.choice inferInstance
  have h0 : (κ₀ (b 1 : K)).im ≠ 0 := orderBasis_im_ne_zero O hc κ₀ b hb
  obtain ⟨κ, hκ⟩ : ∃ κ : K →+* ℂ, 0 < (κ (b 1 : K)).im := by
    rcases lt_or_gt_of_ne h0 with hn | hp
    · refine ⟨ComplexEmbedding.conjugate κ₀, ?_⟩
      simpa only [ComplexEmbedding.conjugate_coe_eq, Complex.conj_im, neg_pos] using hn
    · exact ⟨κ₀, hp⟩
  let z := κ (b 1 : K)
  have hp : z ^ 2 - (t : ℂ) * z + (u : ℂ) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] using congrArg κ hpoly
  have hi := congrArg Complex.im hp
  simp only [pow_two, mul_im, add_im, sub_im, intCast_re, intCast_im, zero_mul,
    add_zero, zero_im] at hi
  have hreal : 2 * z.re = t := by
    have h : (2 * z.re - (t : ℝ)) * z.im = 0 := by linear_combination hi
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hκ.ne')
  have hr := congrArg Complex.re hp
  simp only [pow_two, mul_re, add_re, sub_re, intCast_re, intCast_im, zero_mul,
    sub_zero, zero_re] at hr
  have hdiscR : (t : ℝ)^2 - 4 * (u : ℝ) = (d : ℝ) := by exact_mod_cast hdisc
  have hisq : (2 * z.im)^2 = -(d : ℝ) := by nlinarith [congrArg (· ^ 2) hreal]
  have him : 2 * z.im = Real.sqrt (-(d : ℝ)) := by
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rwa [Real.sq_sqrt (by exact_mod_cast (neg_nonneg.mpr hd.le))]
  have hS : (B : ZMod 2)^2 = (t : ZMod 2)^2 := by
    have h : B^2 - t^2 = 4 * (A * C - u) := by linarith
    have h' : (B : ZMod 2)^2 - (t : ZMod 2)^2 = 4 * ((A : ZMod 2) * C - u) := by
      simpa only [map_sub, map_pow, map_mul, map_ofNat, Int.coe_castRingHom] using
        congrArg (Int.castRingHom (ZMod 2)) h
    rw [show (4 : ZMod 2) = 0 by decide, zero_mul] at h'
    exact sub_eq_zero.mp h'
  have hBt : (B : ZMod 2) = (t : ZMod 2) := by simpa only [ZMod.pow_card] using hS
  have he : (2 : ℤ) ∣ -B - t := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [hBt, sub_eq_add_neg, ← neg_add, ← two_mul, show (2 : ZMod 2) = 0 by decide,
      zero_mul, neg_zero]
  obtain ⟨n, hn⟩ := he
  let ω := (b 1 : K) + (n : K)
  refine ⟨κ, ω, O.toSubalgebra.add_mem (b 1).property
    (O.toSubalgebra.intCast_mem n), ?_, ?_, ?_⟩
  · intro x
    let a := b.repr x 0
    let c := b.repr x 1
    have h := b.sum_repr x
    rw [Fin.sum_univ_two, hb] at h
    have h' := congrArg O.toSubalgebra.val h
    simp only [map_add, zsmul_eq_mul] at h'
    change (a : K) * 1 + (c : K) * (b 1 : K) = (x : K) at h'
    refine ⟨a - c * n, c, ?_⟩
    push_cast
    dsimp [ω]
    linear_combination -h'
  · have hu : u = A * C + n ^ 2 + B * n := by
      have ht : t = -B - 2 * n := by omega
      rw [ht] at hdisc
      linarith [hdisc, hform]
    have huK : (u : K) = (A : K) * (C : K) + (n : K)^2 + (B : K) * (n : K) := by exact_mod_cast hu
    have hnK : -(B : K) - (t : K) = 2 * (n : K) := by exact_mod_cast hn
    dsimp [ω]
    linear_combination hpoly + (b 1 : K) * (-hnK) - huK
  · have hnR : -(B : ℝ) - (t : ℝ) = 2 * (n : ℝ) := by exact_mod_cast hn
    rw [show κ ω = z + (n : ℂ) by simp [ω, z]]
    apply Complex.ext
    · rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, Complex.div_ofReal_re]
      simp [mul_re]
      linarith
    · rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, Complex.div_ofReal_im]
      simp [mul_im]
      linarith

/-- The oriented generator can be chosen in any prescribed complex embedding. -/
theorem exists_heegner_generator_in_embedding (O : NumberFieldOrder K)
    (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K) (κ : K →+* ℂ)
    {A B C d : ℤ} (hD : O.discr = d) (hd : d < 0) (hform : B ^ 2 - 4 * A * C = d) :
    ∃ ω : K, ω ∈ O.toSubalgebra ∧
      (∀ x : O.toSubalgebra, ∃ u v : ℤ, (x : K) = (u : K) + (v : K) * ω) ∧
      (ω ^ 2 + (B : K) * ω + (A : K) * (C : K) = 0) ∧
      κ ω = (-(B : ℂ) + I * (Real.sqrt (-(d : ℝ)) : ℂ)) / 2 := by
  obtain ⟨ι, ω, hω, hgen, hp, he⟩ := exists_heegner_generator O hk hc hD hd hform
  have eval (e : K →+* ℂ) : (e ω) ^ 2 + (B : ℂ) * e ω + (A : ℂ) * (C : ℂ) = 0 := by
    simpa only [map_pow, map_add, map_mul, map_intCast, map_zero] using congrArg e hp
  have hdif : (κ ω - ι ω) * (κ ω + ι ω + (B : ℂ)) = 0 := by
    linear_combination eval κ - eval ι
  rcases mul_eq_zero.mp hdif with hz | hz
  · exact ⟨ω, hω, hgen, hp, (sub_eq_zero.mp hz).trans he⟩
  · let v := -(B : K) - ω
    refine ⟨v, O.toSubalgebra.sub_mem (by simp) hω,
      fun x => ?_, ?_, ?_⟩
    · obtain ⟨a, b, hab⟩ := hgen x
      exact ⟨a - b * B, -b, by rw [hab]; push_cast [v]; ring⟩
    · dsimp [v]
      linear_combination hp
    · dsimp only [v]
      rw [map_sub, map_neg, map_intCast, ← he]
      linear_combination -hz


end ZInQ.Manuscript.RC.CMField2
