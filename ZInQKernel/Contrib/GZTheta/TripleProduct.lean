import ZInQKernel.Contrib.GZTheta.ThetaUnique
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# gz-theta: Jacobi's triple product identity

For `Im τ > 0`, `q = e^{π i τ}` and every `z ∈ ℂ`:

  `θ(z, τ) = ∑_{n ∈ ℤ} e^{2π i n z} q^{n²}
           = ∏_{n ≥ 0} (1 − q^{2n+2}) (1 + q^{2n+1} e^{2π i z}) (1 + q^{2n+1} e^{−2π i z})`

(`jacobiTheta₂_eq_jtpP`), with Mathlib's `jacobiTheta₂`. Proof: both sides are entire in `z` with
the same functional equations, so they are proportional (`ThetaUnique.lean`); the constant
`c(τ)` satisfies `c(τ) = c(4τ)` (compare `z = 1/4` at `τ` with `z = 1/2` at `4τ`) and
`c(τ) → 1` as `Im τ → ∞`.
-/

open Complex Filter
open scoped Real Topology

noncomputable section

namespace ZInQ.GZTheta

/-- `q = e^{π i τ}`. -/
def qJ (τ : ℂ) : ℂ := cexp (π * I * τ)

theorem norm_qJ (τ : ℂ) : ‖qJ τ‖ = Real.exp (-π * τ.im) := by
  rw [qJ, Complex.norm_exp]
  congr 1
  simp [mul_re, mul_im]

theorem norm_qJ_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖qJ τ‖ < 1 := by
  rw [norm_qJ, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])

theorem qJ_ne_zero (τ : ℂ) : qJ τ ≠ 0 := Complex.exp_ne_zero _

/-- `e(z) = e^{2π i z}`. -/
def eJ (z : ℂ) : ℂ := cexp (2 * π * I * z)

theorem norm_eJ (z : ℂ) : ‖eJ z‖ = Real.exp (-2 * π * z.im) := by
  rw [eJ, Complex.norm_exp]
  congr 1
  simp [mul_re, mul_im]

theorem eJ_add (z w : ℂ) : eJ (z + w) = eJ z * eJ w := by
  rw [eJ, eJ, eJ, ← Complex.exp_add]; ring_nf

theorem eJ_one : eJ 1 = 1 := by
  rw [eJ, mul_one, Complex.exp_two_pi_mul_I]

theorem eJ_tau (τ : ℂ) : eJ τ = qJ τ ^ 2 := by
  rw [eJ, qJ, ← Complex.exp_nat_mul]; ring_nf

theorem eJ_neg (z : ℂ) : eJ (-z) = (eJ z)⁻¹ := by
  rw [eJ, eJ, ← Complex.exp_neg]; ring_nf

theorem eJ_ne_zero (z : ℂ) : eJ z ≠ 0 := Complex.exp_ne_zero _

/-! ### The products -/

/-- `∏_{n ≥ 0} (1 + q^{2n+1} e(z))`. -/
def jtpB (τ z : ℂ) : ℂ := ∏' n : ℕ, (1 + qJ τ ^ (2 * n + 1) * eJ z)

/-- `∏_{n ≥ 0} (1 − q^{2n+2})`. -/
def jtpA (τ : ℂ) : ℂ := ∏' n : ℕ, (1 - qJ τ ^ (2 * n + 2))

/-- The triple product. -/
def jtpP (τ z : ℂ) : ℂ := jtpA τ * jtpB τ z * jtpB τ (-z)

theorem summable_geom_odd {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (C : ℝ) :
    Summable (fun n : ℕ => r ^ (2 * n + 1) * C) := by
  have : Summable (fun n : ℕ => (r ^ 2) ^ n) :=
    summable_geometric_of_lt_one (by positivity) (by nlinarith)
  refine (this.mul_right (r * C)).congr fun n => ?_
  ring

theorem summable_jtpB_term {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    Summable (fun n : ℕ => ‖qJ τ ^ (2 * n + 1) * eJ z‖) := by
  simp only [norm_mul, norm_pow]
  exact summable_geom_odd (norm_nonneg _) (norm_qJ_lt_one hτ) _

theorem multipliable_jtpB {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    Multipliable (fun n : ℕ => 1 + qJ τ ^ (2 * n + 1) * eJ z) :=
  multipliable_one_add_of_summable (summable_jtpB_term hτ z)

theorem summable_jtpA_term {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℕ => ‖-qJ τ ^ (2 * n + 2)‖) := by
  simp only [norm_neg, norm_pow]
  refine (summable_geom_odd (norm_nonneg _) (norm_qJ_lt_one hτ) ‖qJ τ‖).congr fun n => ?_
  ring

theorem jtpA_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jtpA τ ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -qJ τ ^ (2 * n + 2))
    (fun n => by
      intro h0
      have : qJ τ ^ (2 * n + 2) = 1 := by linear_combination -h0
      have hn := congrArg norm this
      rw [norm_pow, norm_one] at hn
      have := pow_lt_one₀ (norm_nonneg _) (norm_qJ_lt_one hτ) (by omega : 2 * n + 2 ≠ 0)
      linarith)
    (summable_jtpA_term hτ)
  simpa [jtpA, sub_eq_add_neg] using h

/-! ### Holomorphy in `z` -/

theorem differentiable_jtpB {τ : ℂ} (hτ : 0 < τ.im) : Differentiable ℂ (jtpB τ) := by
  intro z₀
  set R : ℝ := |z₀.im| + 1
  set K : Set ℂ := {z | -R < z.im}
  have hK : IsOpen K := isOpen_lt continuous_const Complex.continuous_im
  have hz₀ : z₀ ∈ K := by
    show -R < z₀.im
    have := neg_abs_le z₀.im
    simp only [R]; linarith
  have hu : Summable (fun n : ℕ => ‖qJ τ‖ ^ (2 * n + 1) * Real.exp (2 * π * R)) :=
    summable_geom_odd (norm_nonneg _) (norm_qJ_lt_one hτ) _
  have hprod := Summable.hasProdLocallyUniformlyOn_nat_one_add
    (f := fun n z => qJ τ ^ (2 * n + 1) * eJ z) hK hu (Filter.Eventually.of_forall fun n z hz => by
      rw [norm_mul, norm_pow, norm_eJ]
      have : -2 * π * z.im ≤ 2 * π * R := by
        have hz : -R < z.im := hz
        have := Real.pi_pos
        nlinarith
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) (by positivity))
    (fun n => by unfold eJ; fun_prop)
  have hd : DifferentiableOn ℂ (jtpB τ) K := by
    refine TendstoLocallyUniformlyOn.differentiableOn hprod (Filter.Eventually.of_forall fun s => ?_) hK
    simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun n _ => by unfold eJ; fun_prop)
  exact hd.differentiableAt (hK.mem_nhds hz₀)

theorem differentiable_jtpP {τ : ℂ} (hτ : 0 < τ.im) : Differentiable ℂ (jtpP τ) := by
  unfold jtpP
  have h1 := differentiable_jtpB hτ
  have h2 : Differentiable ℂ (fun z => jtpB τ (-z)) := h1.comp differentiable_neg
  exact (h1.const_mul _).mul h2

/-! ### Functional equations -/

theorem jtpB_add_one (τ z : ℂ) : jtpB τ (z + 1) = jtpB τ z := by
  simp [jtpB, eJ_add, eJ_one]

theorem jtpP_add_one (τ z : ℂ) : jtpP τ (z + 1) = jtpP τ z := by
  unfold jtpP
  rw [jtpB_add_one, show -(z + 1) = -z + (-1) by ring]
  have : jtpB τ (-z + -1) = jtpB τ (-z) := by
    rw [← jtpB_add_one τ (-z + -1)]; ring_nf
  rw [this]

/-- `B(z) = (1 + q e(z)) B(z + τ)`. -/
theorem jtpB_eq_mul_add_tau {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jtpB τ z = (1 + qJ τ * eJ z) * jtpB τ (z + τ) := by
  have hm := multipliable_jtpB hτ z
  have hm1 : Multipliable (fun n : ℕ => 1 + qJ τ ^ (2 * (n + 1) + 1) * eJ z) :=
    multipliable_one_add_of_summable ((summable_nat_add_iff 1).mpr (summable_jtpB_term hτ z))
  have h := tprod_eq_zero_mul' (f := fun n : ℕ => 1 + qJ τ ^ (2 * n + 1) * eJ z) hm1
  beta_reduce at h
  have htail : (∏' n : ℕ, (1 + qJ τ ^ (2 * (n + 1) + 1) * eJ z)) = jtpB τ (z + τ) := by
    unfold jtpB
    refine tprod_congr fun n => ?_
    rw [eJ_add, eJ_tau τ]
    ring
  unfold jtpB
  rw [h]
  rw [show (∏' n : ℕ, (1 + qJ τ ^ (2 * (n + 1) + 1) * eJ z)) = jtpB τ (z + τ) from htail]
  simp [jtpB]

/-- `B(−z−τ) = (1 + q⁻¹ e(−z)) B(−z)`. -/
theorem jtpB_neg_sub_tau {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jtpB τ (-(z + τ)) = (1 + (qJ τ)⁻¹ * eJ (-z)) * jtpB τ (-z) := by
  have hm := multipliable_jtpB hτ (-(z + τ))
  have hm1 : Multipliable (fun n : ℕ => 1 + qJ τ ^ (2 * (n + 1) + 1) * eJ (-(z + τ))) :=
    multipliable_one_add_of_summable
      ((summable_nat_add_iff 1).mpr (summable_jtpB_term hτ (-(z + τ))))
  have h := tprod_eq_zero_mul' (f := fun n : ℕ => 1 + qJ τ ^ (2 * n + 1) * eJ (-(z + τ))) hm1
  beta_reduce at h
  have hq := qJ_ne_zero τ
  have e1 : eJ (-(z + τ)) = eJ (-z) * (qJ τ ^ 2)⁻¹ := by
    rw [neg_add, eJ_add, eJ_neg τ, eJ_tau τ]
  have h0 : 1 + qJ τ ^ (2 * 0 + 1) * eJ (-(z + τ)) = 1 + (qJ τ)⁻¹ * eJ (-z) := by
    rw [e1]; field_simp; ring
  have htail : (∏' n : ℕ, (1 + qJ τ ^ (2 * (n + 1) + 1) * eJ (-(z + τ)))) = jtpB τ (-z) := by
    unfold jtpB
    refine tprod_congr fun n => ?_
    rw [e1]
    field_simp
    ring
  rw [show jtpB τ (-(z + τ)) = ∏' n : ℕ, (1 + qJ τ ^ (2 * n + 1) * eJ (-(z + τ))) from rfl, h,
    h0, htail]

theorem jtpP_add_tau {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jtpP τ (z + τ) = cexp (-π * I * (τ + 2 * z)) * jtpP τ z := by
  unfold jtpP
  rw [jtpB_neg_sub_tau hτ, jtpB_eq_mul_add_tau hτ z]
  have hexp : cexp (-π * I * (τ + 2 * z)) = (qJ τ)⁻¹ * eJ (-z) := by
    rw [qJ, eJ, ← Complex.exp_neg, ← Complex.exp_add]; ring_nf
  have hq := qJ_ne_zero τ
  have he : eJ (-z) * eJ z = 1 := by rw [eJ_neg, inv_mul_cancel₀ (eJ_ne_zero z)]
  rw [hexp]
  have : (1 + (qJ τ)⁻¹ * eJ (-z)) = (qJ τ)⁻¹ * eJ (-z) * (1 + qJ τ * eJ z) := by
    rw [mul_add, mul_one]
    have h2 : (qJ τ)⁻¹ * eJ (-z) * (qJ τ * eJ z) = eJ (-z) * eJ z := by field_simp
    rw [h2, he]
    ring
  rw [this]
  ring


/-! ### Nonvanishing on the real line -/

theorem one_add_ne_zero_of_norm_lt {w : ℂ} (hw : ‖w‖ < 1) : 1 + w ≠ 0 := by
  intro h
  have : w = -1 := by linear_combination h
  rw [this] at hw
  simp at hw

theorem jtpB_ne_zero_of_real {τ : ℂ} (hτ : 0 < τ.im) (x : ℝ) : jtpB τ x ≠ 0 := by
  refine tprod_one_add_ne_zero_of_summable (fun n => one_add_ne_zero_of_norm_lt ?_)
    (summable_jtpB_term hτ x)
  rw [norm_mul, norm_pow, norm_eJ]
  simp only [ofReal_im, mul_zero, Real.exp_zero, mul_one]
  exact pow_lt_one₀ (norm_nonneg _) (norm_qJ_lt_one hτ) (by omega)

theorem jtpP_ne_zero_of_real {τ : ℂ} (hτ : 0 < τ.im) (x : ℝ) : jtpP τ x ≠ 0 := by
  unfold jtpP
  refine mul_ne_zero (mul_ne_zero (jtpA_ne_zero hτ) (jtpB_ne_zero_of_real hτ x)) ?_
  have := jtpB_ne_zero_of_real hτ (-x)
  simpa using this

/-! ### `θ` is proportional to the product -/

theorem intervalIntegrable_of_differentiable {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    IntervalIntegrable (fun x : ℝ => g x) MeasureTheory.volume 0 1 :=
  (hg.continuous.comp continuous_ofReal).intervalIntegrable _ _

theorem exists_jacobiTheta₂_eq_const_mul {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ c : ℂ, ∀ z, jacobiTheta₂ z τ = c * jtpP τ z := by
  set a := ∫ x : ℝ in (0 : ℝ)..1, jtpP τ x with ha_def
  set b := ∫ x : ℝ in (0 : ℝ)..1, jacobiTheta₂ x τ with hb_def
  have hθd : Differentiable ℂ (fun z => jacobiTheta₂ z τ) :=
    fun z => differentiableAt_jacobiTheta₂_fst z hτ
  have hPd := differentiable_jtpP hτ
  have ha : a ≠ 0 := by
    intro ha0
    have := eq_zero_of_theta_fe (τ := τ) hPd (jtpP_add_one τ) (jtpP_add_tau hτ) ha0
    exact jtpP_ne_zero_of_real hτ 0 (by simpa using congrFun this 0)
  have hf := eq_zero_of_theta_fe (τ := τ) (f := fun z => a * jacobiTheta₂ z τ - b * jtpP τ z)
    ((hθd.const_mul a).sub (hPd.const_mul b))
    (fun z => by simp only [jacobiTheta₂_add_left, jtpP_add_one])
    (fun z => by simp only [jacobiTheta₂_add_left', jtpP_add_tau hτ]; ring)
    (by
      rw [intervalIntegral.integral_sub
        ((intervalIntegrable_of_differentiable hθd).const_mul a)
        ((intervalIntegrable_of_differentiable hPd).const_mul b),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rw [← ha_def, ← hb_def]
      ring)
  refine ⟨b / a, fun z => ?_⟩
  have := congrFun hf z
  simp only [Pi.zero_apply] at this
  field_simp
  linear_combination this

/-- The proportionality constant, read at `z = 1/2`. -/
def jtpC (τ : ℂ) : ℂ := jacobiTheta₂ (1 / 2) τ / jtpP τ (1 / 2)

theorem jtpP_half_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jtpP τ (1 / 2) ≠ 0 := by
  have := jtpP_ne_zero_of_real hτ (1 / 2)
  simpa using this

theorem jacobiTheta₂_eq_jtpC_mul {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiTheta₂ z τ = jtpC τ * jtpP τ z := by
  obtain ⟨c, hc⟩ := exists_jacobiTheta₂_eq_const_mul hτ
  have hcc : c = jtpC τ := by
    rw [jtpC, hc, mul_div_assoc, div_self (jtpP_half_ne_zero hτ), mul_one]
  rw [hc, hcc]

end ZInQ.GZTheta
