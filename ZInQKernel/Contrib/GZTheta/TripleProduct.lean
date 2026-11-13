import ZInQKernel.Contrib.GZTheta.ThetaUnique
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.Normed.Ring.InfiniteProd

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


/-! ### `c(τ) = c(4τ)`: the product side -/

theorem summable_geom_lin {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) (k m : ℕ) (hk : 0 < k) :
    Summable (fun n : ℕ => ‖c * q ^ (k * n + m)‖) := by
  have h1 : ‖q‖ ^ k < 1 := pow_lt_one₀ (norm_nonneg _) hq hk.ne'
  have : Summable (fun n : ℕ => (‖q‖ ^ k) ^ n) :=
    summable_geometric_of_lt_one (by positivity) h1
  refine (this.mul_left (‖c‖ * ‖q‖ ^ m)).congr fun n => ?_
  rw [norm_mul, norm_pow, pow_add, pow_mul]
  ring

theorem multipliable_geom_lin {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) (k m : ℕ) (hk : 0 < k) :
    Multipliable (fun n : ℕ => 1 + c * q ^ (k * n + m)) :=
  multipliable_one_add_of_summable (summable_geom_lin hq c k m hk)

/-- `∏ (1 + c q^{kn+m})`, the shape of all products below. -/
def gp (q c : ℂ) (k m : ℕ) : ℂ := ∏' n : ℕ, (1 + c * q ^ (k * n + m))

theorem gp_mul_gp {q : ℂ} (hq : ‖q‖ < 1) (c d : ℂ) (k m : ℕ) (hk : 0 < k) :
    gp q c k m * gp q d k m = ∏' n : ℕ, ((1 + c * q ^ (k * n + m)) * (1 + d * q ^ (k * n + m))) :=
  ((multipliable_geom_lin hq c k m hk).tprod_mul (multipliable_geom_lin hq d k m hk)).symm

theorem gp_even_mul_odd {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) (k m : ℕ) (hk : 0 < k) :
    gp q c (2 * k) m * gp q c (2 * k) (k + m) = gp q c k m := by
  unfold gp
  rw [← tprod_even_mul_odd (f := fun n : ℕ => 1 + c * q ^ (k * n + m))]
  · congr 1
    · exact tprod_congr fun n => by ring_nf
    · exact tprod_congr fun n => by ring_nf
  · exact (multipliable_geom_lin hq c (2 * k) m (by omega)).congr fun n => by ring_nf
  · exact (multipliable_geom_lin hq c (2 * k) (k + m) (by omega)).congr fun n => by ring_nf

theorem jtpA_eq_gp (τ : ℂ) : jtpA τ = gp (qJ τ) (-1) 2 2 := by
  unfold jtpA gp
  exact tprod_congr fun n => by ring

theorem jtpB_eq_gp (τ z : ℂ) : jtpB τ z = gp (qJ τ) (eJ z) 2 1 := by
  unfold jtpB gp
  exact tprod_congr fun n => by ring

theorem qJ_four_mul (τ : ℂ) : qJ (4 * τ) = qJ τ ^ 4 := by
  rw [qJ, qJ, ← Complex.exp_nat_mul]; ring_nf

theorem gp_pow (q c : ℂ) (j k m : ℕ) : gp (q ^ j) c k m = gp q c (j * k) (j * m) := by
  unfold gp
  exact tprod_congr fun n => by rw [← pow_mul]; ring_nf

theorem eJ_quarter : eJ (1 / 4) = I := by
  rw [eJ, show 2 * (π : ℂ) * I * (1 / 4) = (π / 2 : ℂ) * I by ring, Complex.exp_mul_I]
  rw [show (π : ℂ) / 2 = ((π / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem eJ_half : eJ (1 / 2) = -1 := by
  rw [eJ, show 2 * (π : ℂ) * I * (1 / 2) = π * I by ring, Complex.exp_pi_mul_I]

/-- **The product side of `c(τ) = c(4τ)`**: `P(1/4; τ) = P(1/2; 4τ)`. -/
theorem jtpP_quarter {τ : ℂ} (hτ : 0 < τ.im) : jtpP τ (1 / 4) = jtpP (4 * τ) (1 / 2) := by
  have hq := norm_qJ_lt_one hτ
  set q := qJ τ
  unfold jtpP
  rw [jtpA_eq_gp, jtpA_eq_gp, jtpB_eq_gp, jtpB_eq_gp, jtpB_eq_gp, jtpB_eq_gp, qJ_four_mul,
    eJ_quarter, show -(1 / 4 : ℂ) = (-1 : ℂ) * (1 / 4) by ring,
    show -(1 / 2 : ℂ) = (-1 : ℂ) * (1 / 2) by ring]
  have em : ∀ w : ℂ, eJ ((-1 : ℂ) * w) = (eJ w)⁻¹ := fun w => by rw [neg_one_mul, eJ_neg]
  rw [em, em, eJ_quarter, eJ_half, Complex.inv_I, inv_neg, inv_one]
  simp only [gp_pow]
  norm_num only
  -- left side: `A(q) · ∏(1 + i q^{2n+1}) ∏(1 − i q^{2n+1})`
  rw [mul_assoc, gp_mul_gp hq I (-I) 2 1 (by norm_num)]
  have h1 : (∏' n : ℕ, ((1 + I * q ^ (2 * n + 1)) * (1 + -I * q ^ (2 * n + 1)))) =
      gp q 1 4 2 := by
    unfold gp
    refine tprod_congr fun n => ?_
    have : I * I = -1 := Complex.I_mul_I
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [h1]
  -- `A(q) = ∏(1 − q^{4n+2}) ∏(1 − q^{4n+4})`
  rw [← gp_even_mul_odd hq (-1) 2 2 (by norm_num)]
  norm_num only
  have h2 : gp q (-1) 4 2 * gp q 1 4 2 = gp q (-1) 8 4 := by
    rw [gp_mul_gp hq (-1) 1 4 2 (by norm_num)]
    unfold gp
    refine tprod_congr fun n => ?_
    ring
  have h3 := gp_even_mul_odd hq (-1) 4 4 (by norm_num)
  norm_num only at h3
  rw [show gp q (-1) 4 2 * gp q (-1) 4 4 * gp q 1 4 2 =
    (gp q (-1) 4 2 * gp q 1 4 2) * gp q (-1) 4 4 by ring, h2, ← h3]
  ring

/-! ### `c(τ) = c(4τ)`: the series side -/

theorem jacobiTheta₂_term_quarter_odd (τ : ℂ) (m : ℤ) :
    jacobiTheta₂_term (2 * (-m - 1) + 1) (1 / 4) τ = -jacobiTheta₂_term (2 * m + 1) (1 / 4) τ := by
  unfold jacobiTheta₂_term
  have : 2 * π * I * ((2 * (-m - 1) + 1 : ℤ) : ℂ) * (1 / 4) +
      π * I * ((2 * (-m - 1) + 1 : ℤ) : ℂ) ^ 2 * τ =
      (2 * π * I * ((2 * m + 1 : ℤ) : ℂ) * (1 / 4) + π * I * ((2 * m + 1 : ℤ) : ℂ) ^ 2 * τ) +
        (π * I + ((-m - 1 : ℤ) : ℂ) * (2 * π * I)) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_pi_mul_I]
  ring

/-- **The series side of `c(τ) = c(4τ)`**: `θ(1/4; τ) = θ(1/2; 4τ)`. -/
theorem jacobiTheta₂_quarter {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ (1 / 4) τ = jacobiTheta₂ (1 / 2) (4 * τ) := by
  set f : ℤ → ℂ := fun n => jacobiTheta₂_term n (1 / 4) τ with hfdef
  have hf : HasSum f (jacobiTheta₂ (1 / 4) τ) := hasSum_jacobiTheta₂_term _ hτ
  have h4 : 0 < (4 * τ).im := by simp; linarith
  have he : HasSum (f ∘ fun m : ℤ => 2 * m) (jacobiTheta₂ (1 / 2) (4 * τ)) := by
    refine (hasSum_jacobiTheta₂_term (1 / 2) h4).congr_fun fun m => ?_
    simp only [Function.comp_apply, hfdef, jacobiTheta₂_term]
    congr 1
    push_cast
    ring
  have hos : Summable (f ∘ fun m : ℤ => 2 * m + 1) :=
    hf.summable.comp_injective (fun a b h => by simpa using h)
  have ho : HasSum (f ∘ fun m : ℤ => 2 * m + 1) 0 := by
    let σ : ℤ ≃ ℤ := (Equiv.neg ℤ).trans (Equiv.subRight 1)
    have hσ : ∀ m, σ m = -m - 1 := fun m => rfl
    have hS : ∑' m, (f ∘ fun m : ℤ => 2 * m + 1) m = -∑' m, (f ∘ fun m : ℤ => 2 * m + 1) m := by
      conv_lhs => rw [← σ.tsum_eq]
      rw [← tsum_neg]
      refine tsum_congr fun m => ?_
      simp only [Function.comp_apply, hσ, hfdef]
      exact jacobiTheta₂_term_quarter_odd τ m
    have h0 : ∑' m, (f ∘ fun m : ℤ => 2 * m + 1) m = 0 := by
      have := hS; linear_combination this / 2
    rw [← h0]
    exact hos.hasSum
  have hcompl : IsCompl (Set.range fun m : ℤ => 2 * m) (Set.range fun m : ℤ => 2 * m + 1) := by
    rw [isCompl_iff, disjoint_iff, codisjoint_iff]
    constructor
    · ext n
      simp only [Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_range, Set.bot_eq_empty,
        Set.mem_empty_iff_false, iff_false, not_and, forall_exists_index]
      rintro a rfl ⟨b, hb⟩
      omega
    · ext n
      simp only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Set.top_eq_univ, Set.mem_univ,
        iff_true]
      rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
      · exact Or.inl ⟨k, rfl⟩
      · exact Or.inr ⟨k, rfl⟩
  have he' := (Function.Injective.hasSum_range_iff (f := f)
    (g := fun m : ℤ => 2 * m) (fun a b h => by simpa using h)).mpr he
  have ho' := (Function.Injective.hasSum_range_iff (f := f)
    (g := fun m : ℤ => 2 * m + 1) (fun a b h => by simpa using h)).mpr ho
  have := HasSum.add_isCompl (f := f) hcompl he' ho'
  rw [add_zero] at this
  exact hf.unique this

/-- **`c(τ) = c(4τ)`.** -/
theorem jtpC_four_mul {τ : ℂ} (hτ : 0 < τ.im) : jtpC τ = jtpC (4 * τ) := by
  have h4 : 0 < (4 * τ).im := by simp; linarith
  have e := jacobiTheta₂_eq_jtpC_mul hτ (1 / 4)
  rw [jacobiTheta₂_quarter hτ, jtpP_quarter hτ] at e
  rw [show jtpC (4 * τ) = jacobiTheta₂ (1 / 2) (4 * τ) / jtpP (4 * τ) (1 / 2) from rfl, e,
    mul_div_assoc, div_self (jtpP_half_ne_zero h4), mul_one]


/-! ### `c(τ) → 1` and the triple product identity -/

theorem jacobiTheta₂_half_eq (τ : ℂ) : jacobiTheta₂ (1 / 2) τ = jacobiTheta (τ + 1) := by
  rw [jacobiTheta₂, jacobiTheta]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term]
  obtain ⟨r, hr⟩ := Int.even_mul_pred_self n
  have hn : (n : ℂ) ^ 2 = n + 2 * r := by
    have : ((n * (n - 1) : ℤ) : ℂ) = ((r + r : ℤ) : ℂ) := by rw [hr]
    push_cast at this
    linear_combination this
  have : π * I * (n : ℂ) ^ 2 * (τ + 1) =
      (2 * π * I * n * (1 / 2) + π * I * (n : ℂ) ^ 2 * τ) + (r : ℂ) * (2 * π * I) := by
    rw [mul_add, mul_one, hn]; ring
  rw [this, Complex.exp_add _ ((r : ℂ) * (2 * π * I)), Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem norm_jacobiTheta₂_half_sub_one_le {τ : ℂ} (hτ : 0 < τ.im) :
    ‖jacobiTheta₂ (1 / 2) τ - 1‖ ≤ 2 / (1 - ‖qJ τ‖) * ‖qJ τ‖ := by
  rw [jacobiTheta₂_half_eq, norm_qJ]
  have h1 : 0 < (τ + 1).im := by simpa using hτ
  have := norm_jacobiTheta_sub_one_le h1
  simpa using this

theorem tendsto_gp_nhds_zero (c : ℂ) (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    Tendsto (fun q : ℂ => gp q c k m) (𝓝 0) (𝓝 1) := by
  have := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 (0 : ℂ)) (g := fun _ : ℕ => 0)
    (f := fun (q : ℂ) (n : ℕ) => c * q ^ (k * n + m))
    (bound := fun n : ℕ => ‖c‖ * (1 / 2 : ℝ) ^ (k * n + m))
    ((summable_geom_lin (q := (1 / 2 : ℂ)) (by norm_num) c k m hk).congr fun n => by
      rw [norm_mul, norm_pow]; norm_num)
    (fun n => by
      have : Tendsto (fun q : ℂ => c * q ^ (k * n + m)) (𝓝 0) (𝓝 (c * 0 ^ (k * n + m))) :=
        ((continuous_pow _).tendsto 0).const_mul c
      rwa [zero_pow (by omega), mul_zero] at this)
    (by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with q hq n
      rw [norm_mul, norm_pow]
      gcongr
      simpa using (mem_ball_zero_iff.mp hq).le)
  simpa [gp] using this

theorem jtpP_half_eq_gp (τ : ℂ) :
    jtpP τ (1 / 2) = gp (qJ τ) (-1) 2 2 * gp (qJ τ) (-1) 2 1 * gp (qJ τ) (-1) 2 1 := by
  unfold jtpP
  rw [jtpA_eq_gp, jtpB_eq_gp, jtpB_eq_gp, eJ_half,
    show -(1 / 2 : ℂ) = (1 / 2 : ℂ) + (-1) by ring, eJ_add, eJ_half, eJ_neg, eJ_one]
  norm_num

theorem qJ_four_pow_mul (τ : ℂ) (k : ℕ) : qJ ((4 : ℂ) ^ k * τ) = qJ τ ^ (4 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_comm ((4 : ℂ) ^ k) 4, mul_assoc, qJ_four_mul, ih, ← pow_mul, pow_succ]

/-- **`c(τ) = 1`.** -/
theorem jtpC_eq_one {τ : ℂ} (hτ : 0 < τ.im) : jtpC τ = 1 := by
  set τs : ℕ → ℂ := fun k => (4 : ℂ) ^ k * τ with hτs
  have hpos : ∀ k, 0 < (τs k).im := fun k => by
    simp only [hτs]
    rw [show (4 : ℂ) ^ k = ((4 ^ k : ℕ) : ℂ) by push_cast; ring]
    simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero]
    positivity
  -- `c` is constant along the sequence
  have hconst : ∀ k, jtpC (τs k) = jtpC τ := by
    intro k
    induction k with
    | zero => simp [hτs]
    | succ k ih =>
      rw [← ih, jtpC_four_mul (hpos k)]
      simp only [hτs]
      rw [pow_succ, mul_comm ((4 : ℂ) ^ k) 4, mul_assoc]
  -- `q(τ_k) → 0`
  have hq0 : Tendsto (fun k => qJ (τs k)) atTop (𝓝 0) := by
    have hr := norm_qJ_lt_one hτ
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hle : ∀ k, ‖qJ (τs k)‖ ≤ ‖qJ τ‖ ^ k := by
      intro k
      simp only [hτs]
      rw [qJ_four_pow_mul, norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) hr.le
        (Nat.lt_pow_self (by norm_num : 1 < 4)).le
    exact squeeze_zero (fun k => norm_nonneg _) hle
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hr)
  -- `θ(1/2; τ_k) → 1`
  have hθ : Tendsto (fun k => jacobiTheta₂ (1 / 2) (τs k)) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hn : Tendsto (fun k => ‖qJ (τs k)‖) atTop (𝓝 0) := by
      simpa using hq0.norm
    have hb : Tendsto (fun k => 2 / (1 - ‖qJ (τs k)‖) * ‖qJ (τs k)‖) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := (2 : ℝ))).div
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hn) (by norm_num)).mul hn
      simpa using this
    exact squeeze_zero (fun k => norm_nonneg _)
      (fun k => norm_jacobiTheta₂_half_sub_one_le (hpos k)) hb
  -- `P(1/2; τ_k) → 1`
  have hP : Tendsto (fun k => jtpP (τs k) (1 / 2)) atTop (𝓝 1) := by
    simp only [jtpP_half_eq_gp]
    have h1 := (tendsto_gp_nhds_zero (-1) 2 2 (by norm_num) (by norm_num)).comp hq0
    have h2 := (tendsto_gp_nhds_zero (-1) 2 1 (by norm_num) (by norm_num)).comp hq0
    have := (h1.mul h2).mul h2
    simpa using this
  have hC : Tendsto (fun k => jtpC (τs k)) atTop (𝓝 1) := by
    have := hθ.div hP (by norm_num)
    rw [div_one] at this
    exact this.congr (fun k => rfl)
  have hC' : Tendsto (fun k => jtpC (τs k)) atTop (𝓝 (jtpC τ)) := by
    simp only [hconst]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hC' hC

/-- **Jacobi's triple product identity.** For `Im τ > 0`, `q = e^{π i τ}` and all `z`,
`θ(z, τ) = ∏_{n ≥ 0} (1 − q^{2n+2})(1 + q^{2n+1} e^{2π i z})(1 + q^{2n+1} e^{−2π i z})`. -/
theorem jacobiTheta₂_eq_jtpP {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiTheta₂ z τ = jtpP τ z := by
  rw [jacobiTheta₂_eq_jtpC_mul hτ, jtpC_eq_one hτ, one_mul]

end ZInQ.GZTheta
