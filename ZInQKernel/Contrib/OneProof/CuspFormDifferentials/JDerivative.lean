import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.FunctionField
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.LevelOne
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.Endpoints
import Mathlib.NumberTheory.ModularForms.Derivative

/-! The derivative `j′ = dj/dτ` of the modular invariant on the upper half-plane: it is
holomorphic, of weight two under `SL(2, ℤ)`, its reciprocal is bounded and nonvanishing
near `i∞`, and its germ is nonzero everywhere. For a weight-two cusp form `f` on `Γ₀(N)`
the quotient `f / j′` is then a meromorphic function on `X₀(N)` in the sense of P1. -/

noncomputable section

open Filter UpperHalfPlane ModularCurve ShimuraPointDict Complex
open scoped Topology MatrixGroups ModularForm Manifold

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open X0Model

/-- `j` as a function on `ℂ`, through `ofComplex`. -/
abbrev jFun (z : ℂ) : ℂ := analyticJ (ofComplex z)

/-- The derivative `j′` of the modular invariant. -/
def jDeriv (z : ℂ) : ℂ := deriv jFun z

theorem mdifferentiable_analyticJ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) analyticJ :=
  (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo' ModularForm.discriminant_ne_zero

theorem analyticAt_jFun (τ : ℍ) : AnalyticAt ℂ jFun (τ : ℂ) :=
  analyticOn_j τ τ.im_pos

theorem analyticAt_jDeriv (τ : ℍ) : AnalyticAt ℂ jDeriv (τ : ℂ) :=
  (analyticAt_jFun τ).deriv

theorem analyticOnNhd_jDeriv : AnalyticOnNhd ℂ jDeriv {z : ℂ | 0 < z.im} :=
  fun z hz => analyticAt_jDeriv ⟨z, hz⟩

/-- `j′` has weight two under `SL(2, ℤ)`. -/
theorem jDeriv_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    jDeriv (γ • τ : ℍ) = denom γ τ ^ 2 * jDeriv τ := by
  have hslash : (analyticJ ∣[(0 : ℤ)] γ) = analyticJ := by
    funext σ
    rw [ModularForm.SL_slash_apply, J0Cusps.analyticJ_invariant, zpow_neg, zpow_zero, inv_one,
      mul_one]
  have h := congrFun (Derivative.normalizedDerivOfComplex_SL_slash (k := 0) (γ := γ)
    mdifferentiable_analyticJ) τ
  rw [hslash] at h
  simp only [Pi.sub_apply, Int.cast_zero, zero_mul, zero_add, sub_zero] at h
  rw [ModularForm.SL_slash_apply] at h
  simp only [Derivative.normalizedDerivOfComplex] at h
  have hd := denom_ne_zero γ τ
  have h2 : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h' : deriv (analyticJ ∘ ofComplex) (τ : ℂ) =
      deriv (analyticJ ∘ ofComplex) ((γ • τ : ℍ) : ℂ) * denom γ τ ^ (-(2 : ℤ)) := by
    have := mul_left_cancel₀ h2 (h.trans (mul_assoc _ _ _))
    simpa only [Int.reduceAdd] using this
  change deriv (analyticJ ∘ ofComplex) ((γ • τ : ℍ) : ℂ) =
    denom γ τ ^ 2 * deriv (analyticJ ∘ ofComplex) (τ : ℂ)
  rw [h', zpow_neg, zpow_ofNat]
  field_simp

/-- Near `i∞`, `1/j′` is bounded by one and `j′` does not vanish. -/
theorem jDeriv_cusp : ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, T < z.im →
    jDeriv z ≠ 0 ∧ ‖(jDeriv z)⁻¹‖ ≤ 1 := by
  obtain ⟨U, hU, hU0, hUval⟩ := ModFnClassify.j_cusp_unit
  obtain ⟨r, hr, hUr⟩ := hU.exists_ball_analyticOnNhd
  let q : ℂ → ℂ := Function.Periodic.qParam 1
  let H : ℂ → ℂ := fun w => w / (2 * Real.pi * Complex.I * (w * deriv U w - U w))
  have hHc : ContinuousAt H 0 := by
    have hd : ContinuousAt (fun w => 2 * Real.pi * Complex.I * (w * deriv U w - U w)) 0 :=
      continuousAt_const.mul ((continuousAt_id.mul hU.deriv.continuousAt).sub hU.continuousAt)
    exact continuousAt_id.div hd (by simp [hU0, Real.pi_ne_zero, Complex.I_ne_zero])
  have hden : ∀ᶠ w in 𝓝 (0 : ℂ), 2 * Real.pi * Complex.I * (w * deriv U w - U w) ≠ 0 := by
    have hd : ContinuousAt (fun w => 2 * Real.pi * Complex.I * (w * deriv U w - U w)) 0 :=
      continuousAt_const.mul ((continuousAt_id.mul hU.deriv.continuousAt).sub hU.continuousAt)
    exact hd.eventually_ne (by simp [hU0, Real.pi_ne_zero, Complex.I_ne_zero])
  have hHsmall : ∀ᶠ w in 𝓝 (0 : ℂ), ‖H w‖ < 1 := by
    have : H 0 = 0 := by simp [H]
    exact hHc.eventually (Metric.ball_mem_nhds (H 0) one_pos) |>.mono fun w hw => by
      simpa [this, dist_zero_right] using hw
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hden.and hHsmall).and (Metric.ball_mem_nhds (0 : ℂ) hr))
  -- the threshold
  obtain ⟨T, hT, hTq⟩ : ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, T < z.im → ‖q z‖ < ρ := by
    refine ⟨max 1 (-Real.log ρ / (2 * Real.pi)), lt_max_of_lt_left one_pos, fun z hz => ?_⟩
    rw [Function.Periodic.norm_qParam, div_one]
    have h1 : -Real.log ρ / (2 * Real.pi) < z.im := lt_of_le_of_lt (le_max_right _ _) hz
    have h2 : -2 * Real.pi * z.im < Real.log ρ := by
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp h1
      linarith
    calc Real.exp (-2 * Real.pi * z.im) < Real.exp (Real.log ρ) := Real.exp_lt_exp.mpr h2
      _ = ρ := Real.exp_log hρ
  refine ⟨T, hT, fun z hz => ?_⟩
  have hzpos : 0 < z.im := lt_trans hT hz
  -- local formula `j = U(q)/q` near `z`
  have hq : HasDerivAt q (2 * Real.pi * Complex.I * q z) z := by
    have h := ((hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp
    simp only [id, mul_one] at h
    have he : q = fun w => cexp (2 * Real.pi * Complex.I * w) := by
      funext w; simp [q, Function.Periodic.qParam]
    rw [he]
    convert h using 1
    simp [mul_comm]
  have hqz : q z ≠ 0 := Function.Periodic.qParam_ne_zero z
  have hqball : q z ∈ Metric.ball (0 : ℂ) ρ := by
    simpa [dist_zero_right] using hTq z hz
  obtain ⟨⟨hdz, hHz⟩, hzr⟩ := hball (q z) hqball
  have hUd : HasDerivAt U (deriv U (q z)) (q z) :=
    ((hUr (q z) (by simpa using hzr)).differentiableAt).hasDerivAt
  have hloc : jFun =ᶠ[𝓝 z] fun w => U (q w) / q w := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hzpos] with w hw
    have h : U (q w) = q w * analyticJ (ofComplex w) := hUval (⟨w, hw⟩ : ℍ)
    have hw0 : q w ≠ 0 := Function.Periodic.qParam_ne_zero w
    change analyticJ (ofComplex w) = U (q w) / q w
    rw [eq_div_iff hw0, h, mul_comm]
  have hderiv : HasDerivAt jFun ((deriv U (q z) * (2 * Real.pi * Complex.I * q z) * q z -
      U (q z) * (2 * Real.pi * Complex.I * q z)) / q z ^ 2) z :=
    ((hUd.comp z hq).div hq hqz).congr_of_eventuallyEq hloc
  have hJ : jDeriv z = 2 * Real.pi * Complex.I * (q z * deriv U (q z) - U (q z)) / q z := by
    rw [jDeriv, hderiv.deriv]
    field_simp
  have hJinv : (jDeriv z)⁻¹ = H (q z) := by
    rw [hJ, inv_div]
  constructor
  · intro h0
    rw [hJ, div_eq_zero_iff] at h0
    exact h0.elim hdz hqz
  · rw [hJinv]
    exact hHz.le

/-- The germ of `j′` at a point of `ℍ`, as an element of the local meromorphic field. -/
def jDerivGerm (τ : ℍ) : MeromorphicGerm (τ : ℂ) :=
  ⟨(jDeriv : PuncturedGerm (τ : ℂ)), jDeriv, rfl, (analyticAt_jDeriv τ).meromorphicAt⟩

/-- `j′` is not identically zero near any point of `ℍ`. -/
theorem jDeriv_not_eventually_zero (τ : ℍ) : ¬ (jDeriv =ᶠ[𝓝[≠] (τ : ℂ)] fun _ => 0) := by
  intro h
  obtain ⟨T, hT, hTz⟩ := jDeriv_cusp
  have hconn : IsPreconnected {z : ℂ | 0 < z.im} :=
    (convex_halfSpace_im_gt 0).isPreconnected
  have hev : jDeriv =ᶠ[𝓝 (τ : ℂ)] 0 :=
    ((analyticAt_jDeriv τ).frequently_zero_iff_eventually_zero).mp
      (h.frequently.and_eventually (eventually_mem_nhdsWithin) |>.mono fun _ h => h.1)
  have hzero := analyticOnNhd_jDeriv.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn
    τ.im_pos hev
  have hpt : (0 : ℝ) < ((T + 1 : ℝ) * Complex.I).im := by simp; linarith
  exact (hTz ((T + 1 : ℝ) * Complex.I) (by simp)).1 (hzero hpt)

theorem jDerivGerm_ne_zero (τ : ℍ) : jDerivGerm τ ≠ 0 := by
  intro h
  apply jDeriv_not_eventually_zero τ
  have := congrArg (meromorphicIncl (τ : ℂ)) h
  rw [map_zero] at this
  exact Germ.coe_eq.mp this

section QuotientForm

variable (N : ℕ)

/-- Weight-two cusp forms on `Γ₀(N)`. -/
abbrev CuspFormN : Type := CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2

/-- The quotient `f / j′`, as a function on `ℂ`. -/
def quotientByJDeriv (f : CuspFormN N) (z : ℂ) : ℂ :=
  f (ofComplex z) / jDeriv z

theorem cuspForm_analyticAt (f : CuspFormN N) (τ : ℍ) :
    AnalyticAt ℂ (fun z => f (ofComplex z)) (τ : ℂ) := by
  have hd : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  exact hd.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem cuspForm_smul (f : CuspFormN N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    f (γ • τ) = denom γ τ ^ 2 * f τ := by
  have h := SlashInvariantForm.slash_action_eqn_SL'' f hγ τ
  rw [h, zpow_ofNat]

theorem cuspForm_slash_eq (f : CuspFormN N) (σ : SL(2, ℤ)) (τ : ℍ) :
    f (σ • τ) = ((f : ℍ → ℂ) ∣[(2 : ℤ)] σ) τ * denom σ τ ^ 2 := by
  rw [ModularForm.SL_slash_apply, mul_assoc, zpow_neg, zpow_ofNat,
    inv_mul_cancel₀ (pow_ne_zero 2 (denom_ne_zero _ _)), mul_one]

/-- For a weight-two cusp form `f` on `Γ₀(N)`, `f / j′` is a meromorphic function on
`X₀(N)` in the sense of P1. -/
theorem isX0Function_quotientByJDeriv [NeZero N] (f : CuspFormN N) :
    IsX0Function N (quotientByJDeriv N f) := by
  obtain ⟨T, hT, hTj⟩ := jDeriv_cusp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ((cuspForm_analyticAt N f ⟨z, hz⟩).meromorphicAt).div
      (analyticAt_jDeriv ⟨z, hz⟩).meromorphicAt
  · intro γ hγ τ
    simp only [quotientByJDeriv, ofComplex_apply]
    rw [cuspForm_smul N f hγ τ, jDeriv_smul γ τ]
    have hd := pow_ne_zero 2 (denom_ne_zero γ τ)
    rw [mul_div_mul_left _ _ hd]
  · intro σ
    refine ⟨0, ?_⟩
    have hval : (fun τ : ℍ => Function.Periodic.qParam N τ ^ 0 *
        quotientByJDeriv N f (σ • τ : ℍ)) =
        fun τ : ℍ => ((f : ℍ → ℂ) ∣[(2 : ℤ)] σ) τ * (jDeriv τ)⁻¹ := by
      funext τ
      simp only [pow_zero, one_mul, quotientByJDeriv, ofComplex_apply]
      rw [cuspForm_slash_eq N f σ τ, jDeriv_smul σ τ]
      have hd := pow_ne_zero 2 (denom_ne_zero σ τ)
      rw [mul_comm (denom _ _ ^ 2) (jDeriv τ), mul_div_mul_right _ _ hd, div_eq_mul_inv]
    rw [hval]
    have hb : IsBoundedAtImInfty (fun τ : ℍ => (jDeriv τ)⁻¹) := by
      refine isBoundedAtImInfty_iff.mpr ⟨1, T + 1, fun τ hτ => ?_⟩
      exact (hTj τ (by rw [UpperHalfPlane.coe_im]; linarith)).2
    exact (ModularFormClass.bdd_at_infty_slash f σ).mul hb
  · intro σ
    have hev : ∀ᶠ z : ℂ in comap Complex.im atTop, T < z.im :=
      (eventually_gt_atTop T).comap Complex.im
    filter_upwards [hev] with z hz
    have hzpos : 0 < z.im := lt_trans hT hz
    let τ : ℍ := ⟨z, hzpos⟩
    let A := Matrix.SpecialLinearGroup.mapGL ℝ σ
    have hA : 0 < A.val.det := by
      change 0 < (A.det : ℝ)
      rw [show A.det = 1 from Matrix.SpecialLinearGroup.det_mapGL σ]
      norm_num
    have ha : AnalyticAt ℂ (fun w => ((σ • ofComplex w : ℍ) : ℂ)) z :=
      τ.analyticAt_smul hA
    have hστ : ((σ • ofComplex z : ℍ) : ℂ) = ((σ • τ : ℍ) : ℂ) := by
      rw [show ofComplex z = τ from ofComplex_apply_of_im_pos hzpos]
    have hne : jDeriv ((σ • τ : ℍ) : ℂ) ≠ 0 := by
      rw [jDeriv_smul σ τ]
      exact mul_ne_zero (pow_ne_zero 2 (denom_ne_zero σ τ)) (hTj z hz).1
    have hq : DifferentiableAt ℂ (quotientByJDeriv N f) ((σ • ofComplex z : ℍ) : ℂ) := by
      rw [hστ]
      exact ((cuspForm_analyticAt N f (σ • τ)).differentiableAt).div
        (analyticAt_jDeriv (σ • τ)).differentiableAt hne
    exact hq.comp z ha.differentiableAt

end QuotientForm

end ZInQ.Manuscript.RC.CuspFormDifferentials
