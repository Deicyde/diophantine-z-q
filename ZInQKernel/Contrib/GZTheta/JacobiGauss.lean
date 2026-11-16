import ZInQKernel.Contrib.GZTheta.TripleProduct

/-!
# gz-theta: Jacobi's `η³` identity and Gauss's identity, from the triple product

With `q = e^{π i τ}`, `A = ∏_{n ≥ 0} (1 − q^{2n+2})`:

* (Jacobi) `∑_{n ∈ ℤ} n e^{2π i n z₀} q^{n²} = A³` at `z₀ = (1 + τ)/2`, i.e.
  `∑_n n (−1)^n q^{n² + n} = ∏ (1 − q^{2n+2})³`: differentiate the triple product at its zero
  `z₀` (`hasSum_jacobi`).
* (Gauss) `∑_n (−1)^n q^{n²} = ∏ (1 − q^{2n+2}) (1 − q^{2n+1})²` (`z = 1/2`; `hasSum_gauss`).
-/

open Complex Filter
open scoped Real Topology

noncomputable section

namespace ZInQ.GZTheta

/-- `P(z) = (1 + q e(−z)) · A B(z) B(τ − z)`. -/
theorem jtpP_eq_factor {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jtpP τ z = (1 + qJ τ * eJ (-z)) * (jtpA τ * jtpB τ z * jtpB τ (τ - z)) := by
  unfold jtpP
  rw [jtpB_eq_mul_add_tau hτ (-z), show -z + τ = τ - z by ring]
  ring

theorem eJ_half_tau (τ : ℂ) : eJ (τ / 2) = qJ τ := by
  rw [eJ, qJ]; ring_nf

theorem eJ_neg_half : eJ (-(1 / 2)) = -1 := by
  rw [eJ_neg, eJ_half]; norm_num

theorem jtpB_at_z0 {τ : ℂ} (w : ℂ) (hw : eJ w = -qJ τ) : jtpB τ w = jtpA τ := by
  unfold jtpB jtpA
  refine tprod_congr fun n => ?_
  rw [hw]
  ring

/-- **Jacobi's identity**: `∑_{n ∈ ℤ} n · e^{2π i n z₀ + π i n² τ} = A³`, `z₀ = (1 + τ)/2`. -/
theorem hasSum_jacobi {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => (n : ℂ) * jacobiTheta₂_term n ((1 + τ) / 2) τ) (jtpA τ ^ 3) := by
  set z₀ : ℂ := (1 + τ) / 2 with hz₀
  have hq := qJ_ne_zero τ
  -- values at `z₀`
  have e1 : eJ (-z₀) = -(qJ τ)⁻¹ := by
    rw [hz₀, show -((1 + τ) / 2) = -(1 / 2) + -(τ / 2) by ring, eJ_add, eJ_neg_half, eJ_neg,
      eJ_half_tau]
    ring
  have e2 : eJ z₀ = -qJ τ := by
    rw [hz₀, show (1 + τ) / 2 = 1 / 2 + τ / 2 by ring, eJ_add, eJ_half, eJ_half_tau]; ring
  have e3 : eJ (τ - z₀) = -qJ τ := by
    rw [hz₀, show τ - (1 + τ) / 2 = τ / 2 + -(1 / 2) by ring, eJ_add, eJ_half_tau, eJ_neg_half]
    ring
  -- derivative of the product at `z₀`
  set R : ℂ → ℂ := fun z => jtpA τ * jtpB τ z * jtpB τ (τ - z) with hR
  have hRd : DifferentiableAt ℂ R z₀ := by
    have h1 := differentiable_jtpB hτ
    have h2 : Differentiable ℂ (fun z => jtpB τ (τ - z)) := h1.comp (differentiable_const _ |>.sub
      differentiable_id)
    exact ((h1.const_mul _).mul h2) z₀
  have hF : HasDerivAt (fun z => 1 + qJ τ * eJ (-z)) (qJ τ * (eJ (-z₀) * (2 * π * I * -1))) z₀ := by
    have h := (((hasDerivAt_id z₀).neg).const_mul (2 * π * I)).cexp
    have h' := (h.const_mul (qJ τ)).const_add 1
    simpa [eJ, mul_comm, mul_left_comm, mul_assoc] using h'
  have hP : HasDerivAt (jtpP τ) (2 * π * I * jtpA τ ^ 3) z₀ := by
    have hmul := hF.mul hRd.hasDerivAt
    have hfun : ((fun z => 1 + qJ τ * eJ (-z)) * R) = jtpP τ := by
      funext z; rw [Pi.mul_apply, jtpP_eq_factor hτ z]
    rw [hfun] at hmul
    convert hmul using 1
    rw [e1]
    have hR0 : R z₀ = jtpA τ ^ 3 := by
      simp only [hR]; rw [jtpB_at_z0 z₀ e2, jtpB_at_z0 (τ - z₀) e3]; ring
    rw [hR0]
    field_simp
    ring
  -- the same derivative from the series
  have hθ : HasDerivAt (jtpP τ) (jacobiTheta₂' z₀ τ) z₀ := by
    have h := hasDerivAt_jacobiTheta₂_fst z₀ hτ
    have hfun : (fun z => jacobiTheta₂ z τ) = jtpP τ := funext (jacobiTheta₂_eq_jtpP hτ)
    rwa [hfun] at h
  have heq : jacobiTheta₂' z₀ τ = 2 * π * I * jtpA τ ^ 3 := hθ.unique hP
  have hs := hasSum_jacobiTheta₂'_term z₀ hτ
  rw [heq] at hs
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have := hs.div_const (2 * π * I)
  rw [mul_div_cancel_left₀ _ h2pi] at this
  refine this.congr_fun fun n => ?_
  simp only [jacobiTheta₂'_term]
  field_simp

/-- **Gauss's identity**: `∑_{n ∈ ℤ} e^{π i n + π i n² τ} = A ∏(1 − q^{2n+1})²` (`z = 1/2`). -/
theorem hasSum_gauss {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => jacobiTheta₂_term n (1 / 2) τ)
      (gp (qJ τ) (-1) 2 2 * gp (qJ τ) (-1) 2 1 * gp (qJ τ) (-1) 2 1) := by
  rw [← jtpP_half_eq_gp, ← jacobiTheta₂_eq_jtpP hτ]
  exact hasSum_jacobiTheta₂_term _ hτ

end ZInQ.GZTheta
