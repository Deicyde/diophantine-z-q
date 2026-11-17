import ZInQKernel.Contrib.OneProof.Gamma0QExp.QSeries
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_hasSum_jNum_qParam
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_E4_cube_div_discriminant_smul
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.Modular

/-!
# gamma0-qexp, part 3: growth, `j`, and holomorphic level-one functions

* `ModGrowth F`: `F(τ) = O(e^{2πk Im τ})` as `Im τ → ∞`; closed under ring operations.
* `j = E₄³/Δ`: invariant, holomorphic, `½ e^{2π Im τ} ≤ |j(τ)| ≤ 2 e^{2π Im τ}` for `Im τ` large.
* **Level one, holomorphic** (`levelOne_hol`): an `SL₂(ℤ)`-invariant holomorphic `G` on `ℍ` with
  `ModGrowth G` is a polynomial in `j`. Proof: `q^k G` is bounded at `∞`, so has a `q`-expansion on
  all of `ℍ` (Mathlib's `hasSum_qExpansion`); subtract a polynomial in `j` to kill the principal
  part; the rest is constant (FLT's `coeff_eq_zero_of_hasSum_of_slash_invariant`).

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane ModularCurve Filter Topology Asymptotics
open scoped MatrixGroups Manifold


namespace ZInQ.Gamma0QExp

/-! ### Moderate growth at `∞` -/

/-- `F(τ) = O(e^{2πk Im τ})` as `Im τ → ∞`, for some `k`. -/
def ModGrowth (F : ℍ → ℂ) : Prop :=
  ∃ k : ℕ, F =O[atImInfty] fun τ => Real.exp (2 * Real.pi * k * τ.im)

theorem expGrowth_mono {k l : ℕ} (h : k ≤ l) :
    (fun τ : ℍ => Real.exp (2 * Real.pi * k * τ.im)) =O[atImInfty]
      fun τ => Real.exp (2 * Real.pi * l * τ.im) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  have hkl : (k : ℝ) ≤ l := by exact_mod_cast h
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkl (by positivity)) τ.im_pos.le

namespace ModGrowth

variable {F G : ℍ → ℂ}

theorem of_le {k l : ℕ} (h : k ≤ l)
    (hF : F =O[atImInfty] fun τ => Real.exp (2 * Real.pi * k * τ.im)) :
    F =O[atImInfty] fun τ => Real.exp (2 * Real.pi * l * τ.im) :=
  hF.trans (expGrowth_mono h)

theorem const (c : ℂ) : ModGrowth (fun _ => c) :=
  ⟨0, by simpa using (isBigO_const_const c (one_ne_zero (α := ℝ)) atImInfty)⟩

theorem add (hF : ModGrowth F) (hG : ModGrowth G) : ModGrowth (fun τ => F τ + G τ) := by
  obtain ⟨k, hk⟩ := hF
  obtain ⟨l, hl⟩ := hG
  exact ⟨max k l, (of_le (le_max_left k l) hk).add (of_le (le_max_right k l) hl)⟩

theorem mul (hF : ModGrowth F) (hG : ModGrowth G) : ModGrowth (fun τ => F τ * G τ) := by
  obtain ⟨k, hk⟩ := hF
  obtain ⟨l, hl⟩ := hG
  refine ⟨k + l, (hk.mul hl).congr_right fun τ => ?_⟩
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

theorem neg (hF : ModGrowth F) : ModGrowth (fun τ => -F τ) := by
  obtain ⟨k, hk⟩ := hF
  exact ⟨k, hk.neg_left⟩

theorem sub (hF : ModGrowth F) (hG : ModGrowth G) : ModGrowth (fun τ => F τ - G τ) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem pow (hF : ModGrowth F) (n : ℕ) : ModGrowth (fun τ => F τ ^ n) := by
  induction n with
  | zero => simpa using const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hF

theorem polyEval (hF : ModGrowth F) (p : Polynomial ℂ) :
    ModGrowth (fun τ => p.eval (F τ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
    simpa only [Polynomial.eval_monomial] using (const a).mul (hF.pow n)

theorem mvEval {σ : Type*} (F : σ → ℍ → ℂ) (h : ∀ i, ModGrowth (F i)) (p : MvPolynomial σ ℂ) :
    ModGrowth (fun τ => MvPolynomial.eval (fun i => F i τ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using const a
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul, MvPolynomial.eval_X] using hp.mul (h i)

/-- A concrete bound. -/
theorem exists_bound (hF : ModGrowth F) :
    ∃ (k : ℕ) (C T : ℝ), ∀ τ : ℍ, T ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (2 * Real.pi * k * τ.im) := by
  obtain ⟨k, hk⟩ := hF
  obtain ⟨C, hC⟩ := hk.bound
  obtain ⟨T, hT⟩ := (atImInfty_mem _).1 hC
  refine ⟨k, C, T, fun τ hτ => ?_⟩
  have := hT τ hτ
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at this
  exact this

end ModGrowth

/-! ### Klein's `j` -/

theorem jf_smul (γ : SL(2, ℤ)) (τ : ℍ) : jf (γ • τ) = jf τ :=
  E4_cube_div_discriminant_smul γ τ

theorem norm_qParam_one (τ : ℍ) : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
  rw [Function.Periodic.norm_qParam, div_one, coe_im]
  ring_nf

theorem qParam_ne_zero (z : ℂ) : Function.Periodic.qParam 1 z ≠ 0 := Complex.exp_ne_zero _

theorem hasSum_qjf (τ : ℍ) : HasSum (fun m : ℕ => ((PowerSeries.coeff m jNum : ℤ) : ℂ) *
    Function.Periodic.qParam 1 (τ : ℂ) ^ m) (Function.Periodic.qParam 1 (τ : ℂ) * jf τ) :=
  hasSum_jNum_qParam τ

theorem tendsto_qjf : Tendsto (fun τ : ℍ => Function.Periodic.qParam 1 (τ : ℂ) * jf τ) atImInfty (𝓝 1) := by
  have := P2MW.S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.ModularCurve.Realized.tendsto_atImInfty
    one_pos hasSum_qjf
  simpa [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum] using this

/-- `½ e^{2π Im τ} ≤ |j(τ)| ≤ 2 e^{2π Im τ}` for `Im τ ≥ T₁`. -/
theorem jf_bounds : ∃ T₁ : ℝ, ∀ τ : ℍ, T₁ ≤ τ.im →
    Real.exp (2 * Real.pi * τ.im) / 2 ≤ ‖jf τ‖ ∧ ‖jf τ‖ ≤ 2 * Real.exp (2 * Real.pi * τ.im) := by
  have h := (tendsto_qjf.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)))
  obtain ⟨T, hT⟩ := (atImInfty_mem _).1 h
  refine ⟨T, fun τ hτ => ?_⟩
  have h1 : ‖Function.Periodic.qParam 1 (τ : ℂ) * jf τ - 1‖ < 1 / 2 := by
    have := hT τ hτ
    simpa [Metric.mem_ball, dist_eq_norm] using this
  have h2 : 1 / 2 ≤ ‖Function.Periodic.qParam 1 (τ : ℂ) * jf τ‖ := by
    have := norm_sub_norm_le (1 : ℂ) (Function.Periodic.qParam 1 (τ : ℂ) * jf τ)
    rw [norm_one, norm_sub_rev] at this
    linarith
  have h3 : ‖Function.Periodic.qParam 1 (τ : ℂ) * jf τ‖ ≤ 2 := by
    have := norm_le_norm_add_norm_sub' (Function.Periodic.qParam 1 (τ : ℂ) * jf τ) 1
    rw [norm_one] at this
    linarith
  rw [norm_mul, norm_qParam_one] at h2 h3
  have he : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpos := Real.exp_pos (2 * Real.pi * τ.im)
  constructor
  · nlinarith
  · nlinarith

theorem jf_modGrowth : ModGrowth jf := by
  obtain ⟨T₁, hT₁⟩ := jf_bounds
  refine ⟨1, IsBigO.of_bound 2 ((atImInfty_mem _).2 ⟨T₁, fun τ hτ => ?_⟩)⟩
  simp only [Set.mem_ofPred_eq, Nat.cast_one, mul_one, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact (hT₁ τ hτ).2

theorem jf_differentiableAt (τ : ℍ) : DifferentiableAt ℂ (jf ∘ ofComplex) (τ : ℂ) := by
  have hmd := P2MW.S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.ModularCurve.Realized.mdifferentiable
    one_pos hasSum_qjf
  have h1 := mdifferentiableAt_iff.mp (hmd τ)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Function.Periodic.qParam 1 z) (τ : ℂ) :=
    (Function.Periodic.differentiable_qParam (h := 1)) _
  refine (h1.div h2 (qParam_ne_zero _)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  simp only [Function.comp_apply, Pi.div_apply, ofComplex_apply_of_im_pos hz]
  exact (mul_div_cancel_left₀ _ (qParam_ne_zero z)).symm

theorem jf_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := fun τ =>
  mdifferentiableAt_iff.mpr (jf_differentiableAt τ)

/-! ### `q`-series of a polynomial in `j` -/

theorem Rz.one : Rz 1 (fun _ => 1) := by
  simpa [HahnSeries.C_apply] using Rz.C 1

theorem Rz.pow {L : LaurentSeries ℂ} {F : ℍ → ℂ} (hL : Rz L F) (n : ℕ) :
    Rz (L ^ n) (fun τ => F τ ^ n) := by
  induction n with
  | zero => simpa using Rz.one
  | succ n ih => simpa only [pow_succ] using ih.mul hL

theorem Rz.polyAeval {L : LaurentSeries ℂ} {F : ℍ → ℂ} (hL : Rz L F) (p : Polynomial ℂ) :
    Rz (Polynomial.aeval L p) (fun τ => p.eval (F τ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add, Polynomial.eval_add] using hp.add hq
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Polynomial.eval_monomial,
      algebraMap_laurentSeries_eq_single]
    have := (Rz.single 0 a).mul (hL.pow n)
    simpa only [zpow_zero, mul_one] using this

/-! ### Killing the principal part with a polynomial in `j` -/

theorem coeffEmb_jq_pow_self (n : ℕ) : (coeffEmb ℂ jq ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [← map_pow, coeffEmb_coeff_eq, coeff_jq_pow_self]; simp

theorem coeffEmb_jq_pow_of_lt {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) :
    (coeffEmb ℂ jq ^ n).coeff m = 0 := by
  rw [← map_pow, coeffEmb_coeff_eq, coeff_jq_pow_of_lt hm]; simp

theorem exists_poly_kill (n : ℕ) : ∀ L : LaurentSeries ℂ, (∀ m : ℤ, m < -(n : ℤ) → L.coeff m = 0) →
    ∃ P : Polynomial ℂ, ∀ m : ℤ, m < 0 → (L - Polynomial.aeval (coeffEmb ℂ jq) P).coeff m = 0 := by
  induction n with
  | zero => exact fun L hL => ⟨0, fun m hm => by simpa using hL m (by simpa using hm)⟩
  | succ n ih =>
    intro L hL
    set c := L.coeff (-((n + 1 : ℕ) : ℤ))
    obtain ⟨P, hP⟩ := ih (L - HahnSeries.C c * coeffEmb ℂ jq ^ (n + 1)) (fun m hm => by
      rw [HahnSeries.coeff_sub, coeff_C_mul]
      rcases lt_or_eq_of_le (show m ≤ -((n + 1 : ℕ) : ℤ) by push_cast at hm ⊢; omega) with h | h
      · rw [hL m h, coeffEmb_jq_pow_of_lt h, mul_zero, sub_zero]
      · rw [h, coeffEmb_jq_pow_self, mul_one, sub_self])
    refine ⟨P + Polynomial.C c * Polynomial.X ^ (n + 1), fun m hm => ?_⟩
    have := hP m hm
    rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      algebraMap_laurentSeries_eq_single]
    rw [← HahnSeries.C_apply]
    convert this using 2
    ring

/-! ### Level one, holomorphic -/

theorem periodic_of_invariant {G : ℍ → ℂ} (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), G (γ • τ) = G τ)
    (k : ℕ) : Function.Periodic ((fun τ : ℍ => Function.Periodic.qParam 1 (τ : ℂ) ^ k * G τ) ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + 1).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, ofComplex_apply_of_im_pos hw']
    have hT : (⟨w + 1, hw'⟩ : ℍ) = ModularGroup.T • (⟨w, hw⟩ : ℍ) := by
      apply UpperHalfPlane.ext
      rw [modular_T_smul]
      simp [add_comm]
    rw [hT, hinv]
    congr 2
    simp only [Function.Periodic.qParam, UpperHalfPlane.coe_mk, Complex.ofReal_one, div_one]
    rw [show (2 : ℂ) * Real.pi * Complex.I * (w + 1) = 2 * Real.pi * Complex.I * w +
      2 * Real.pi * Complex.I by ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  · push Not at hw
    have hw' : (w + 1).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_eq_of_im_nonpos hw' hw]

/-- **Level one, holomorphic.** -/
theorem levelOne_hol (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), G (γ • τ) = G τ) (hgr : ModGrowth G) :
    ∃ P : Polynomial ℂ, ∀ τ : ℍ, G τ = P.eval (jf τ) := by
  obtain ⟨k, hk⟩ := hgr
  set f : ℍ → ℂ := fun τ => Function.Periodic.qParam 1 (τ : ℂ) ^ k * G τ
  have hfper := periodic_of_invariant hinv k
  have hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    have hq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Function.Periodic.qParam 1 (τ : ℂ) ^ k) := fun τ =>
      mdifferentiableAt_iff.mpr <| by
        refine (((Function.Periodic.differentiable_qParam (h := 1)) (τ : ℂ)).pow k).congr_of_eventuallyEq ?_
        filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
        simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, Pi.pow_apply,
          UpperHalfPlane.coe_mk]
    exact hq.mul hG
  have hfbdd : IsBoundedAtImInfty f := by
    have hq : (fun τ : ℍ => Function.Periodic.qParam 1 (τ : ℂ) ^ k) =O[atImInfty]
        fun τ => Real.exp (-(2 * Real.pi * k * τ.im)) := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
      rw [norm_pow, norm_qParam_one, one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        ← Real.exp_nat_mul]
      exact le_of_eq (by ring_nf)
    have := hq.mul hk
    refine this.trans (IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_))
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    simp
  have hsum := fun τ => hasSum_qExpansion (h := 1) one_pos hfper hfhol hfbdd τ
  -- the Laurent series of `G`
  set c := qExpansion 1 f
  set L : LaurentSeries ℂ := HahnSeries.single (-(k : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℂ c
  have hc : Rz (HahnSeries.ofPowerSeries ℤ ℂ c) f := fun τ => by
    rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff]
    · convert hsum τ using 1
      funext n
      simp only [Function.comp_apply, HahnSeries.ofPowerSeries_apply_coeff, zpow_natCast,
        smul_eq_mul]
    · intro m hm
      have hm0 : m < 0 := by
        by_contra h0; push Not at h0; exact hm ⟨m.toNat, Int.toNat_of_nonneg h0⟩
      rw [ofPowerSeries_coeff_of_neg _ hm0, zero_mul]
  have hL : Rz L G := by
    have := (Rz.single (-(k : ℤ)) (1 : ℂ)).mul hc
    refine this.congr_fun fun τ => ?_
    simp only [f, one_mul, zpow_neg, zpow_natCast, ← mul_assoc]
    rw [inv_mul_cancel₀ (pow_ne_zero _ (qParam_ne_zero _)), one_mul]
  -- kill the principal part
  obtain ⟨P, hP⟩ := exists_poly_kill k L (fun m hm => by
    simp only [L, HahnSeries.coeff_single_mul, one_mul]
    exact ofPowerSeries_coeff_of_neg _ (by omega))
  set L' := L - Polynomial.aeval (coeffEmb ℂ jq) P
  have hL' : Rz L' (fun τ => G τ - P.eval (jf τ)) := hL.sub (rz_jq.polyAeval P)
  have hsum' : ∀ τ : ℍ, HasSum (fun n : ℕ => L'.coeff n * Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (G τ - P.eval (jf τ)) := fun τ => by
    have h := hL' τ
    rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff] at h
    · convert h using 1
      funext n
      simp only [Function.comp_apply, zpow_natCast]
    · intro m hm
      have hm0 : m < 0 := by
        by_contra h0; push Not at h0; exact hm ⟨m.toNat, Int.toNat_of_nonneg h0⟩
      rw [hP m hm0, zero_mul]
  have hinv' : ∀ (γ : SL(2, ℤ)) (τ : ℍ), G (γ • τ) - P.eval (jf (γ • τ)) =
      G τ - P.eval (jf τ) := fun γ τ => by rw [hinv, jf_smul]
  have hzero : ∀ n : ℕ, n ≠ 0 → L'.coeff n = 0 := fun n hn =>
    coeff_eq_zero_of_hasSum_of_slash_invariant hsum' hinv' hn
  refine ⟨P + Polynomial.C (L'.coeff 0), fun τ => ?_⟩
  have h1 := hsum' τ
  have h2 : HasSum (fun n : ℕ => L'.coeff n * Function.Periodic.qParam 1 (τ : ℂ) ^ n) (L'.coeff 0) := by
    convert hasSum_single (f := fun n : ℕ => L'.coeff n * Function.Periodic.qParam 1 (τ : ℂ) ^ n) 0
      (fun n hn => by rw [hzero n hn, zero_mul]) using 1
    simp
  have := h1.unique h2
  rw [Polynomial.eval_add, Polynomial.eval_C]
  push_cast at this
  linear_combination this

end ZInQ.Gamma0QExp
