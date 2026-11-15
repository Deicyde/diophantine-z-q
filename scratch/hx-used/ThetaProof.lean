import ZInQKernel.Contrib.OneProof.X0ModuliUsed.EtaRoute

/-! hx-used, scratch: towards a proof of `X0EtaRoute.ThetaWeierstrass8`.
Part M1: the odd theta function `th1(z) = e^{πiz} θ(z + (1+τ)/2; τ)`. -/

noncomputable section

set_option maxRecDepth 20000

namespace X0Theta

open Complex ZInQ.GZTheta
open scoped Real

/-- `c₀ = (1 + τ)/2`. -/
def c0 (τ : ℂ) : ℂ := (1 + τ) / 2

/-- The odd theta function `th1(z) = e^{πiz} θ(z + (1+τ)/2; τ)` (`= i q^{-1/4} θ₁(πz)` classically). -/
def th1 (τ z : ℂ) : ℂ := cexp (π * I * z) * jacobiTheta₂ (z + c0 τ) τ

theorem exp_sub_pi_I (X : ℂ) : cexp (X - π * I) = -cexp X := by
  rw [Complex.exp_sub, Complex.exp_pi_mul_I, div_neg, div_one]

theorem exp_add_pi_I (X : ℂ) : cexp (X + π * I) = -cexp X := by
  rw [Complex.exp_add, Complex.exp_pi_mul_I, mul_neg, mul_one]

theorem th1_add_one (τ z : ℂ) : th1 τ (z + 1) = -th1 τ z := by
  unfold th1
  rw [show z + 1 + c0 τ = (z + c0 τ) + 1 by ring, jacobiTheta₂_add_left,
    show (π : ℂ) * I * (z + 1) = π * I * z + π * I by ring, exp_add_pi_I]
  ring

theorem th1_add_tau (τ z : ℂ) :
    th1 τ (z + τ) = -cexp (-π * I * τ - 2 * π * I * z) * th1 τ z := by
  unfold th1
  rw [show z + τ + c0 τ = (z + c0 τ) + τ by ring, jacobiTheta₂_add_left', ← mul_assoc, ← Complex.exp_add]
  have hE : cexp (π * I * (z + τ) + -π * I * (τ + 2 * (z + c0 τ))) =
      -cexp (-π * I * τ - 2 * π * I * z) * cexp (π * I * z) := by
    rw [show π * I * (z + τ) + -π * I * (τ + 2 * (z + c0 τ)) =
      (-π * I * τ - 2 * π * I * z + π * I * z) - π * I by unfold c0; ring, exp_sub_pi_I, Complex.exp_add]
    ring
  rw [hE]; ring

theorem th1_neg (τ z : ℂ) : th1 τ (-z) = -th1 τ z := by
  unfold th1
  have hA : jacobiTheta₂ (z + c0 τ) τ =
      cexp (-π * I * (τ + 2 * (z - c0 τ + 1))) * jacobiTheta₂ (z - c0 τ) τ := by
    have h1 := jacobiTheta₂_add_left' ((z - c0 τ) + 1) τ
    rwa [jacobiTheta₂_add_left, show z - c0 τ + 1 + τ = z + c0 τ by unfold c0; ring] at h1
  have hE : cexp (π * I * (-z)) = -(cexp (π * I * z) * cexp (-π * I * (τ + 2 * (z - c0 τ + 1)))) := by
    rw [← Complex.exp_add, show π * I * z + -π * I * (τ + 2 * (z - c0 τ + 1)) = π * I * (-z) - π * I by
      unfold c0; ring, exp_sub_pi_I, neg_neg]
  rw [show -z + c0 τ = -(z - c0 τ) by ring, jacobiTheta₂_neg_left, hA, hE]
  ring

theorem th1_zero (τ : ℂ) : th1 τ 0 = 0 := by
  have h := th1_neg τ 0
  rw [neg_zero] at h
  linear_combination h / 2

theorem eJ_half_tau (τ : ℂ) : eJ (τ / 2) = qJ τ := by unfold eJ qJ; congr 1; ring

theorem eJ_c0 (τ z : ℂ) : eJ (z + c0 τ) = -qJ τ * eJ z := by
  rw [c0, show z + (1 + τ) / 2 = z + 1 / 2 + τ / 2 by ring, eJ_add, eJ_add, eJ_half, eJ_half_tau]; ring

theorem two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, I_ne_zero]

theorem eq_int_of_eJ_eq_one {u : ℂ} (h : eJ u = 1) : ∃ k : ℤ, u = k := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨k, mul_right_cancel₀ two_pi_I_ne_zero ?_⟩
  rw [← hk]; ring

/-- `B(z + c₀) = ∏(1 − q^{2n+2}e(z)) ≠ 0` unless `z ∈ −(n+1)τ + ℤ`. -/
theorem jtpB_c0_ne_zero {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ)
    (hz : ∀ (k : ℤ) (n : ℕ), z ≠ k - ((n : ℂ) + 1) * τ) : jtpB τ (z + c0 τ) ≠ 0 := by
  unfold jtpB
  refine tprod_one_add_ne_zero_of_summable (fun n => ?_) (summable_jtpB_term hτ _)
  intro h0
  rw [eJ_c0] at h0
  have h1 : qJ τ ^ (2 * n + 2) * eJ z = 1 := by linear_combination -h0
  have h3 : eJ (((n : ℂ) + 1) * τ) = qJ τ ^ (2 * n + 2) := by
    unfold eJ qJ; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : eJ (z + ((n : ℂ) + 1) * τ) = 1 := by rw [eJ_add, h3, mul_comm]; exact h1
  obtain ⟨k, hk⟩ := eq_int_of_eJ_eq_one h2
  exact hz k n (by linear_combination hk)

/-- **Product form**: `th1(z) = (1 − e(−z))·e^{πiz}·A·B(z + c₀)·B(−z + c₀)`. -/
theorem th1_eq_prod {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    th1 τ z = (1 - eJ (-z)) *
      (cexp (π * I * z) * jtpA τ * jtpB τ (z + c0 τ) * jtpB τ (-z + c0 τ)) := by
  unfold th1
  rw [jacobiTheta₂_eq_jtpP hτ]
  unfold jtpP
  have hB : jtpB τ (-(z + c0 τ)) = (1 - eJ (-z)) * jtpB τ (-z + c0 τ) := by
    have h := jtpB_neg_sub_tau hτ (z + (1 - τ) / 2)
    rw [show z + (1 - τ) / 2 + τ = z + c0 τ by unfold c0; ring] at h
    rw [h]
    have e1 : 1 + (qJ τ)⁻¹ * eJ (-(z + (1 - τ) / 2)) = 1 - eJ (-z) := by
      rw [show -(z + (1 - τ) / 2) = -z + (-(1 / 2)) + τ / 2 by ring, eJ_add, eJ_add, eJ_half_tau,
        eJ_neg (1 / 2), eJ_half]
      field_simp [qJ_ne_zero τ]
      ring
    have e2 : jtpB τ (-(z + (1 - τ) / 2)) = jtpB τ (-z + c0 τ) := by
      rw [← jtpB_add_one τ (-(z + (1 - τ) / 2))]
      congr 1; unfold c0; ring
    rw [e1, e2]
  rw [hB]; ring

theorem th1_ne_zero {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) (hz : ∀ m n : ℤ, z ≠ m + n * τ) :
    th1 τ z ≠ 0 := by
  rw [th1_eq_prod hτ]
  refine mul_ne_zero ?_ (mul_ne_zero (mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _)
    (jtpA_ne_zero hτ)) (jtpB_c0_ne_zero hτ z ?_)) (jtpB_c0_ne_zero hτ (-z) ?_))
  · intro h
    obtain ⟨k, hk⟩ := eq_int_of_eJ_eq_one (sub_eq_zero.1 h).symm
    exact hz (-k) 0 (by push_cast; linear_combination -hk)
  · intro k n h
    exact hz k (-((n : ℤ) + 1)) (by rw [h]; push_cast; ring)
  · intro k n h
    exact hz (-k) ((n : ℤ) + 1) (by push_cast; linear_combination -h)

theorem jtpB_c0_zero_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jtpB τ (c0 τ) ≠ 0 := by
  have := jtpB_c0_ne_zero hτ 0 (fun k n h => by
    have := congrArg Complex.im h
    simp at this
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rcases this with h' | h' <;> linarith)
  simpa using this

theorem differentiable_th1 {τ : ℂ} (hτ : 0 < τ.im) : Differentiable ℂ (th1 τ) := by
  intro z
  unfold th1
  refine DifferentiableAt.mul ?_ ?_
  · exact (differentiableAt_id.const_mul _).cexp
  · exact (differentiableAt_jacobiTheta₂_fst (z + c0 τ) hτ).comp z (differentiableAt_id.add_const _)

/-- **`th1'(0) = 2πi·A·B(c₀)² ≠ 0`.** -/
theorem hasDerivAt_th1_zero {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (th1 τ) (2 * π * I * (jtpA τ * jtpB τ (c0 τ) * jtpB τ (c0 τ))) 0 := by
  have hf : th1 τ = fun z => (1 - eJ (-z)) *
      (cexp (π * I * z) * jtpA τ * jtpB τ (z + c0 τ) * jtpB τ (-z + c0 τ)) :=
    funext (th1_eq_prod hτ)
  rw [hf]
  have h1 : HasDerivAt (fun z : ℂ => 1 - eJ (-z)) (2 * π * I) 0 := by
    have : HasDerivAt (fun z : ℂ => cexp (2 * π * I * -z)) (cexp (2 * π * I * -0) * (2 * π * I * -1)) 0 :=
      ((hasDerivAt_id (0 : ℂ)).neg.const_mul (2 * π * I)).cexp
    have h := this.const_sub 1
    simp only [mul_neg, neg_zero, mul_zero, Complex.exp_zero, one_mul, mul_one, neg_neg] at h
    convert h using 1
    funext x; unfold eJ; congr 2; ring
  have hB := differentiable_jtpB hτ
  have h2 : DifferentiableAt ℂ (fun z : ℂ =>
      cexp (π * I * z) * jtpA τ * jtpB τ (z + c0 τ) * jtpB τ (-z + c0 τ)) 0 := by
    refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul
      (differentiableAt_id.const_mul _).cexp (differentiableAt_const _)) ?_) ?_
    · exact (hB _).comp _ (differentiableAt_id.add_const _)
    · exact (hB _).comp _ (differentiableAt_id.neg.add_const _)
  have := h1.mul h2.hasDerivAt
  convert this using 1
  simp [eJ]

theorem th1_deriv_zero_ne_zero {τ : ℂ} (hτ : 0 < τ.im) :
    (2 * π * I * (jtpA τ * jtpB τ (c0 τ) * jtpB τ (c0 τ)) : ℂ) ≠ 0 :=
  mul_ne_zero two_pi_I_ne_zero (mul_ne_zero (mul_ne_zero (jtpA_ne_zero hτ)
    (jtpB_c0_zero_ne_zero hτ)) (jtpB_c0_zero_ne_zero hτ))

/-- Translation by `m ∈ ℤ`. -/
theorem th1_add_int (τ : ℂ) (m : ℤ) (z : ℂ) : th1 τ (z + m) = (-1) ^ m * th1 τ z := by
  induction m using Int.induction_on generalizing z with
  | zero => simp
  | succ k ih =>
    rw [show z + ((k + 1 : ℤ) : ℂ) = (z + ((k : ℤ) : ℂ)) + 1 by push_cast; ring, th1_add_one, ih,
      zpow_add_one₀ (by norm_num)]
    ring
  | pred k ih =>
    have h := th1_add_one τ (z + ((-k - 1 : ℤ) : ℂ))
    rw [show z + ((-k - 1 : ℤ) : ℂ) + 1 = z + ((-k : ℤ) : ℂ) by push_cast; ring, ih] at h
    rw [zpow_sub_one₀ (by norm_num)]
    linear_combination h

/-- Translation by `nτ`, `n ∈ ℤ`. -/
theorem th1_add_int_tau (τ : ℂ) (n : ℤ) (z : ℂ) :
    th1 τ (z + n * τ) = (-1) ^ n * cexp (-π * I * n ^ 2 * τ - 2 * π * I * n * z) * th1 τ z := by
  induction n using Int.induction_on generalizing z with
  | zero => simp
  | succ k ih =>
    rw [show z + ((k + 1 : ℤ) : ℂ) * τ = (z + ((k : ℤ) : ℂ) * τ) + τ by push_cast; ring, th1_add_tau, ih,
      zpow_add_one₀ (by norm_num)]
    have : cexp (-π * I * τ - 2 * π * I * (z + ((k : ℤ) : ℂ) * τ)) *
        cexp (-π * I * ((k : ℤ) : ℂ) ^ 2 * τ - 2 * π * I * ((k : ℤ) : ℂ) * z) =
        cexp (-π * I * ((k + 1 : ℤ) : ℂ) ^ 2 * τ - 2 * π * I * ((k + 1 : ℤ) : ℂ) * z) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← this]; ring
  | pred k ih =>
    have h := th1_add_tau τ (z + ((-k - 1 : ℤ) : ℂ) * τ)
    rw [show z + ((-k - 1 : ℤ) : ℂ) * τ + τ = z + ((-k : ℤ) : ℂ) * τ by push_cast; ring, ih] at h
    rw [zpow_sub_one₀ (by norm_num)]
    have hE : cexp (-π * I * τ - 2 * π * I * (z + ((-k - 1 : ℤ) : ℂ) * τ)) *
        cexp (-π * I * ((-k - 1 : ℤ) : ℂ) ^ 2 * τ - 2 * π * I * ((-k - 1 : ℤ) : ℂ) * z) =
        cexp (-π * I * ((-k : ℤ) : ℂ) ^ 2 * τ - 2 * π * I * ((-k : ℤ) : ℂ) * z) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hne : cexp (-π * I * τ - 2 * π * I * (z + ((-k - 1 : ℤ) : ℂ) * τ)) ≠ 0 := Complex.exp_ne_zero _
    rw [← hE] at h
    have h' : th1 τ (z + ((-k - 1 : ℤ) : ℂ) * τ) = (-1) ^ (-(k : ℤ)) * (-1)⁻¹ *
        cexp (-π * I * ((-k - 1 : ℤ) : ℂ) ^ 2 * τ - 2 * π * I * ((-k - 1 : ℤ) : ℂ) * z) * th1 τ z := by
      apply mul_left_cancel₀ hne
      linear_combination h
    rw [h']

end X0Theta
