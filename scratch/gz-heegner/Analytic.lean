import ZInQKernel.Contrib.OneProof.GrossZagierHeegner
import ZInQKernel.Contrib.OneProof.RingClassLattice

/-! gz-heegner development: the analytic glue (copies of the definitions of `Heegner.lean`). -/

noncomputable section

open UpperHalfPlane Complex
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm cmPoint)
open scoped MatrixGroups
open ZInQ.Contrib.TYZGenus.Shimura ZInQ.Contrib.TYZGenus.CM HeckeRing.GL2 WeierstrassCurve
  ZInQ.Contrib.TYZDecomp.CurveA
open scoped WeierstrassCurve.Affine Manifold ModularForm

namespace ZInQ.GZHeegner

/-- `g` is **regular at `τ`** (holomorphic in a neighbourhood, with value `g τ`). -/
def RegularAt (g : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : Prop :=
  AnalyticAt ℂ (g ∘ UpperHalfPlane.ofComplex) (τ : ℂ)

section Param

variable (E : WeierstrassCurve ℚ) (L : PeriodPair) {N : ℕ} [NeZero N] (f : Newform N 2) (c : ℚ)

/-- `z(τ) = c·φ_f(τ) ∈ ℂ`, the parameter of `φ(τ) ∈ ℂ/L`. -/
def zPar (τ : UpperHalfPlane) : ℂ := (c : ℂ) * ZInQ.GZHL3.eichler f τ

/-- `x(φ(τ)) = ℘_L(c φ_f(τ)) − b₂/12` (junk at the poles `c φ_f(τ) ∈ L`). -/
def xPar (τ : UpperHalfPlane) : ℂ := L.weierstrassP (zPar f c τ) - (E⁄ℂ).b₂ / 12

/-- `y(φ(τ)) = (℘'_L(c φ_f(τ)) − a₁x − a₃)/2`. -/
def yPar (τ : UpperHalfPlane) : ℂ :=
  (L.derivWeierstrassP (zPar f c τ) - (E⁄ℂ).a₁ * xPar E L f c τ - (E⁄ℂ).a₃) / 2

open Classical in
/-- `1/(x(φ(τ)) − t)`, `0` at the poles of `x∘φ`. -/
def gPar (t : ℚ) (τ : UpperHalfPlane) : ℂ :=
  if zPar f c τ ∈ L.lattice then 0 else (xPar E L f c τ - t)⁻¹

end Param

/-- The hypotheses shared by the analytic glue: `E/ℚ` with the L-series of the newform `f` of
level `N`, trivial character, `L` the period lattice of `E`, `c ∈ ℚ^×` with `c Λ_f ⊆ L`. -/
def ParamSetting (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N] (f : Newform N 2) (L : PeriodPair)
    (c : ℚ) : Prop :=
  f.χ = 1 ∧ (∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) ∧
    ZInQ.GZHL3.IsPeriodLattice E L ∧ c ≠ 0 ∧ ZInQ.GZHL3.PeriodsIn f c L

/-- **(GLUE, analysis) Meromorphy and regularity of the coordinates of `φ`.** `x∘φ`, `y∘φ` and
`1/(x∘φ − t)` are meromorphic on `ℍ`; `x∘φ`, `y∘φ` are regular where `c φ_f(τ) ∉ L`, and
`1/(x∘φ − t)` (value `0` at the poles of `x∘φ`) is regular where `c φ_f(τ) ∈ L` or `x(φ(τ)) ≠ t`.
Content: `φ_f` is holomorphic on `ℍ` (Hecke's bound `aₙ(f) = O(n)`; Mathlib
`ModularForms/Bounds.lean`), `℘_L` is holomorphic off `L` with a double pole at each point of `L`
(Mathlib `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`). -/
def ParamRegular : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2)
    (L : PeriodPair) (c : ℚ), ParamSetting E f L c →
    (∀ τ : UpperHalfPlane, MeromorphicAt (xPar E L f c ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ∧
      MeromorphicAt (yPar E L f c ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ∧
      ∀ t : ℚ, MeromorphicAt (gPar E L f c t ∘ UpperHalfPlane.ofComplex) (τ : ℂ)) ∧
    (∀ τ : UpperHalfPlane, zPar f c τ ∉ L.lattice →
      RegularAt (xPar E L f c) τ ∧ RegularAt (yPar E L f c) τ) ∧
    (∀ (t : ℚ) (τ : UpperHalfPlane), (zPar f c τ ∈ L.lattice ∨ xPar E L f c τ ≠ t) →
      RegularAt (gPar E L f c t) τ)

/-- `q = e^{2πiτ}` as a function of `w ∈ ℂ`. -/
def qC (w : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * w)

theorem norm_qC_lt_one {w : ℂ} (hw : 0 < w.im) : ‖qC w‖ < 1 := by
  rw [qC, Complex.norm_exp]
  have : (2 * Real.pi * Complex.I * w).re = -(2 * Real.pi * w.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  calc Real.exp (-(2 * Real.pi * w.im)) < Real.exp 0 :=
        Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
    _ = 1 := Real.exp_zero

/-- Every `r ∈ [0, 1)` is `|q(τ)|` for some `τ ∈ ℍ`... (for `r > 0`). -/
theorem exists_qC_norm {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ τ : UpperHalfPlane, ‖qC τ‖ = r := by
  have hl : 0 < -Real.log r := by
    have := Real.log_neg hr0 hr1; linarith
  refine ⟨⟨Complex.I * ((-Real.log r / (2 * Real.pi) : ℝ) : ℂ), ?_⟩, ?_⟩
  · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, zero_add]
    exact div_pos hl (by positivity)
  · rw [qC, Complex.norm_exp]
    show Real.exp (2 * Real.pi * Complex.I * (Complex.I * ((-Real.log r / (2 * Real.pi) : ℝ) : ℂ))).re = r
    have : (2 * Real.pi * Complex.I * (Complex.I * ((-Real.log r / (2 * Real.pi) : ℝ) : ℂ))).re =
        Real.log r := by
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
      field_simp
      ring
    rw [this, Real.exp_log hr0]


/-! ## The Weierstrass side: `℘`, `℘'` and `1/(℘ − c₀)` as functions on `ℂ` -/

section Wp

variable (L : PeriodPair)

theorem analyticAt_wp {z : ℂ} (hz : z ∉ L.lattice) : AnalyticAt ℂ L.weierstrassP z :=
  L.differentiableOn_weierstrassP.analyticAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)

theorem analyticAt_dwp {z : ℂ} (hz : z ∉ L.lattice) : AnalyticAt ℂ L.derivWeierstrassP z :=
  L.analyticOnNhd_derivWeierstrassP z hz

theorem meromorphicAt_inv_pow (z₀ : ℂ) (n : ℕ) : MeromorphicAt (fun z : ℂ => 1 / (z - z₀) ^ n) z₀ :=
  (MeromorphicAt.const 1 z₀).div (((MeromorphicAt.id z₀).sub (MeromorphicAt.const z₀ z₀)).pow n)

theorem meromorphicAt_wp (z₀ : ℂ) : MeromorphicAt L.weierstrassP z₀ := by
  by_cases h : z₀ ∈ L.lattice
  · have e : L.weierstrassP =
        fun z => L.weierstrassPExcept z₀ z + (1 / (z - z₀) ^ 2 - 1 / z₀ ^ 2) :=
      funext fun z => (L.weierstrassPExcept_add ⟨z₀, h⟩ z).symm
    rw [e]
    exact (L.analyticAt_weierstrassPExcept z₀).meromorphicAt.add
      ((meromorphicAt_inv_pow z₀ 2).sub (MeromorphicAt.const _ z₀))
  · exact (analyticAt_wp L h).meromorphicAt

theorem meromorphicAt_dwp (z₀ : ℂ) : MeromorphicAt L.derivWeierstrassP z₀ := by
  by_cases h : z₀ ∈ L.lattice
  · have e : L.derivWeierstrassP =
        fun z => L.derivWeierstrassPExcept z₀ z - 2 * (1 / (z - z₀) ^ 3) :=
      funext fun z => by rw [← L.derivWeierstrassPExcept_sub ⟨z₀, h⟩ z]; ring
    rw [e]
    exact (L.analyticAt_derivWeierstrassPExcept z₀).meromorphicAt.sub
      ((MeromorphicAt.const 2 z₀).mul (meromorphicAt_inv_pow z₀ 3))
  · exact (analyticAt_dwp L h).meromorphicAt

open Classical in
/-- `z ↦ 1/(℘(z) − c₀)`, `0` on `L`. -/
def phiT (c₀ : ℂ) (z : ℂ) : ℂ := if z ∈ L.lattice then 0 else (L.weierstrassP z - c₀)⁻¹

theorem analyticAt_phiT_of_mem (c₀ : ℂ) {z₀ : ℂ} (h : z₀ ∈ L.lattice) :
    AnalyticAt ℂ (phiT L c₀) z₀ := by
  set A : ℂ → ℂ := fun z => L.weierstrassPExcept z₀ z - 1 / z₀ ^ 2 - c₀ with hAdef
  have hA : AnalyticAt ℂ A z₀ := (L.analyticAt_weierstrassPExcept z₀).sub analyticAt_const
    |>.sub analyticAt_const
  set R : ℂ → ℂ := fun z => (z - z₀) ^ 2 / (1 + (z - z₀) ^ 2 * A z) with hRdef
  have hR : AnalyticAt ℂ R z₀ := by
    apply AnalyticAt.div
    · fun_prop
    · exact analyticAt_const.add (((analyticAt_id.sub analyticAt_const).pow 2).mul hA)
    · simp
  apply hR.congr
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds z₀] with z hz
  by_cases hzz : z = z₀
  · subst hzz; simp [phiT, h, R]
  · have hzL : z ∉ L.lattice := fun hz' => hz ⟨hz', hzz⟩
    have hw : z - z₀ ≠ 0 := sub_ne_zero.2 hzz
    simp only [phiT, hzL, if_false, R, A]
    rw [← L.weierstrassPExcept_add ⟨z₀, h⟩ z]
    have : L.weierstrassPExcept z₀ z + (1 / (z - z₀) ^ 2 - 1 / z₀ ^ 2) - c₀ =
        (1 + (z - z₀) ^ 2 * (L.weierstrassPExcept z₀ z - 1 / z₀ ^ 2 - c₀)) / (z - z₀) ^ 2 := by
      field_simp; ring
    rw [this, inv_div]

theorem phiT_eventuallyEq {c₀ z₀ : ℂ} (h : z₀ ∉ L.lattice) :
    phiT L c₀ =ᶠ[nhds z₀] fun z => (L.weierstrassP z - c₀)⁻¹ := by
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds h] with z hz
  simp only [phiT, if_neg (show z ∉ L.lattice from hz)]

theorem analyticAt_phiT_of_ne (c₀ : ℂ) {z₀ : ℂ} (h : z₀ ∉ L.lattice)
    (hne : L.weierstrassP z₀ ≠ c₀) : AnalyticAt ℂ (phiT L c₀) z₀ :=
  (((analyticAt_wp L h).sub analyticAt_const).inv (sub_ne_zero.2 hne)).congr
    (phiT_eventuallyEq L h).symm

theorem meromorphicAt_phiT (c₀ z₀ : ℂ) : MeromorphicAt (phiT L c₀) z₀ := by
  by_cases h : z₀ ∈ L.lattice
  · exact (analyticAt_phiT_of_mem L c₀ h).meromorphicAt
  · exact (((meromorphicAt_wp L z₀).sub (MeromorphicAt.const c₀ z₀)).inv).congr
      ((phiT_eventuallyEq L h).symm.filter_mono nhdsWithin_le_nhds)

end Wp

/-! ## The Eichler integral is holomorphic on `ℍ` -/

section Eichler

variable {N : ℕ} [NeZero N] (f : Newform N 2)

/-- The coefficients of `φ_f = Σ aₙ/n qⁿ`. -/
def eCoeff (n : ℕ) : ℂ := if n = 0 then 0 else ZInQ.GZDecomp.coeff f n / n

/-- `φ_f` as a power series in `q`. -/
def eSeries : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (eCoeff f)

theorem hasSum_newform (τ : UpperHalfPlane) :
    HasSum (fun n => ZInQ.GZDecomp.coeff f n * qC τ ^ n) (f.toCuspForm τ) := by
  have h := ModularForm.hasSum_qExpansion f.toCuspForm one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) τ
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = qC τ := by
    simp [Function.Periodic.qParam, qC]
  rw [hq] at h
  exact h

theorem coeff_zero_newform : ZInQ.GZDecomp.coeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f.toCuspForm one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)

theorem eSeries_radius (r : NNReal) (hr : (r : ℝ) < 1) : (r : ENNReal) ≤ (eSeries f).radius := by
  rcases eq_or_lt_of_le r.2 with h0 | h0
  · have : r = 0 := by ext; exact h0.symm
    rw [this]; simp
  obtain ⟨σ, hσ⟩ := exists_qC_norm h0 hr
  apply (eSeries f).le_radius_of_tendsto (l := 0)
  have ht := ((hasSum_newform f σ).summable.tendsto_atTop_zero).norm
  simp only [norm_zero] at ht
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) ht
  rw [eSeries, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, hσ]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  unfold eCoeff
  split_ifs with hn
  · simp
  · rw [norm_div]
    have h1 : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
      rw [Complex.norm_natCast]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    exact div_le_self (norm_nonneg _) h1

theorem eSeries_mem_ball {w : ℂ} (hw : ‖w‖ < 1) : w ∈ Metric.eball (0 : ℂ) (eSeries f).radius := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hw
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr1.le
  set r' : NNReal := ⟨r, hr0⟩
  rw [Metric.mem_eball, edist_zero_right]
  calc (‖w‖₊ : ENNReal) < (r' : ENNReal) := by rw [ENNReal.coe_lt_coe]; exact_mod_cast hr1
    _ ≤ _ := eSeries_radius f r' hr2

theorem eSeries_radius_pos : 0 < (eSeries f).radius := by
  have := eSeries_mem_ball f (w := 0) (by simp)
  rw [Metric.mem_eball] at this; exact lt_of_le_of_lt bot_le this

theorem eichler_eq (τ : UpperHalfPlane) : ZInQ.GZHL3.eichler f τ = (eSeries f).sum (qC τ) := by
  have hs := (eSeries f).hasSum (eSeries_mem_ball f (norm_qC_lt_one τ.im_pos))
  simp only [eSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hs
  have h1 := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.range_one, Finset.sum_singleton, eCoeff] at h1
  unfold ZInQ.GZHL3.eichler
  refine (HasSum.tsum_eq ?_)
  convert h1 using 1
  · funext n
    rw [if_neg (Nat.succ_ne_zero n), qC, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  · simp [eSeries]

theorem analyticAt_eSum {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ (eSeries f).sum w :=
  ((eSeries f).hasFPowerSeriesOnBall (eSeries_radius_pos f)).analyticAt_of_mem
    (eSeries_mem_ball f hw)

theorem analyticAt_qC (w : ℂ) : AnalyticAt ℂ qC w := by unfold qC; fun_prop

theorem eichler_ofComplex_eventuallyEq (τ : UpperHalfPlane) :
    (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (τ : ℂ)]
      fun w => (eSeries f).sum (qC w) := by
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  filter_upwards [hopen.mem_nhds τ.im_pos] with w hw
  simp only [Function.comp_apply]
  rw [eichler_eq, UpperHalfPlane.ofComplex_apply_of_im_pos hw]

theorem analyticAt_eichler (τ : UpperHalfPlane) :
    AnalyticAt ℂ (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex) τ :=
  ((analyticAt_eSum f (norm_qC_lt_one τ.im_pos)).comp (analyticAt_qC _)).congr
    (eichler_ofComplex_eventuallyEq f τ).symm

theorem analyticAt_zPar (c : ℚ) (τ : UpperHalfPlane) :
    AnalyticAt ℂ (zPar f c ∘ UpperHalfPlane.ofComplex) τ :=
  show AnalyticAt ℂ (fun w => (c : ℂ) * (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex) w) τ from
    analyticAt_const.mul (analyticAt_eichler f τ)

theorem zPar_ofComplex (c : ℚ) (τ : UpperHalfPlane) :
    (zPar f c ∘ UpperHalfPlane.ofComplex) (τ : ℂ) = zPar f c τ := by
  simp [UpperHalfPlane.ofComplex_apply]

end Eichler

/-- **`ParamRegular`, proved.** -/
theorem paramRegular : ParamRegular := by
  intro E _ N _ f L c _
  set b : ℂ := (E⁄ℂ).b₂ / 12 with hb
  have hz := analyticAt_zPar f c
  have hval := zPar_ofComplex f c
  have ex : xPar E L f c ∘ UpperHalfPlane.ofComplex =
      (fun z => L.weierstrassP z - b) ∘ (zPar f c ∘ UpperHalfPlane.ofComplex) := rfl
  have ey : yPar E L f c ∘ UpperHalfPlane.ofComplex =
      (fun z => (L.derivWeierstrassP z - (E⁄ℂ).a₁ * (L.weierstrassP z - b) - (E⁄ℂ).a₃) / 2) ∘
        (zPar f c ∘ UpperHalfPlane.ofComplex) := rfl
  have eg : ∀ t : ℚ, gPar E L f c t ∘ UpperHalfPlane.ofComplex =
      phiT L (b + t) ∘ (zPar f c ∘ UpperHalfPlane.ofComplex) := by
    intro t; funext w; simp only [Function.comp_apply, gPar, phiT, xPar, sub_sub, hb]
  have mx : ∀ z₀, MeromorphicAt (fun z => L.weierstrassP z - b) z₀ := fun z₀ =>
    (meromorphicAt_wp L z₀).sub (MeromorphicAt.const _ _)
  have my : ∀ z₀, MeromorphicAt (fun z => (L.derivWeierstrassP z - (E⁄ℂ).a₁ *
      (L.weierstrassP z - b) - (E⁄ℂ).a₃) / 2) z₀ := fun z₀ =>
    (((meromorphicAt_dwp L z₀).sub ((MeromorphicAt.const _ _).mul (mx z₀))).sub
      (MeromorphicAt.const _ _)).div (MeromorphicAt.const _ _)
  refine ⟨fun τ => ⟨?_, ?_, fun t => ?_⟩, fun τ hτ => ⟨?_, ?_⟩, fun t τ h => ?_⟩
  · rw [ex]; exact (mx _).comp_analyticAt (hz τ)
  · rw [ey]; exact (my _).comp_analyticAt (hz τ)
  · rw [eg]; exact (meromorphicAt_phiT L _ _).comp_analyticAt (hz τ)
  · show AnalyticAt ℂ _ _
    rw [ex]
    refine AnalyticAt.comp ?_ (hz τ)
    rw [hval]
    exact (analyticAt_wp L hτ).sub analyticAt_const
  · show AnalyticAt ℂ _ _
    rw [ey]
    refine AnalyticAt.comp ?_ (hz τ)
    rw [hval]
    exact ((((analyticAt_dwp L hτ).sub (analyticAt_const.mul ((analyticAt_wp L hτ).sub
      analyticAt_const))).sub analyticAt_const).div analyticAt_const two_ne_zero)
  · show AnalyticAt ℂ _ _
    rw [eg]
    refine AnalyticAt.comp ?_ (hz τ)
    rw [hval]
    rcases h with h | h
    · exact analyticAt_phiT_of_mem L _ h
    · by_cases hm : zPar f c τ ∈ L.lattice
      · exact analyticAt_phiT_of_mem L _ hm
      · refine analyticAt_phiT_of_ne L _ hm ?_
        intro he; apply h; simp only [xPar, ← hb, he]; ring


/-! ## Power series converging on the unit disc -/

section PSeries

/-- A power series converging on the unit disc has `‖cₙ‖ rⁿ` bounded for each `r < 1`. -/
theorem pseries_bound (c : ℕ → ℂ) (hc : ∀ q : ℂ, ‖q‖ < 1 → Summable (fun n => c n * q ^ n))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : ∃ C, ∀ n, ‖c n‖ * r ^ n ≤ C := by
  have hs := (hc (r : ℂ) (by rw [Complex.norm_real, Real.norm_of_nonneg hr0]; exact hr1))
  have ht := hs.tendsto_atTop_zero.norm
  simp only [norm_zero] at ht
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  refine ⟨C, fun n => ?_⟩
  have := hC ⟨n, rfl⟩
  simpa [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0] using this

/-- Absolute convergence of a dominated power series inside the unit disc. -/
theorem pseries_summable_norm (c d : ℕ → ℂ) (hc : ∀ q : ℂ, ‖q‖ < 1 → Summable (fun n => c n * q ^ n))
    (K : ℝ) (hK : 0 ≤ K) (k : ℕ) (hd : ∀ n, ‖d n‖ ≤ K * (n : ℝ) ^ k * ‖c n‖) {q : ℂ}
    (hq : ‖q‖ < 1) : Summable (fun n => ‖d n‖ * ‖q‖ ^ n) := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hq
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr1
  obtain ⟨C, hC⟩ := pseries_bound c hc hr0.le hr2
  have hρ : ‖‖q‖ / r‖ < 1 := by
    rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hr0.le), div_lt_one hr0]; exact hr1
  have hgeo := (summable_pow_mul_geometric_of_norm_lt_one k hρ).mul_left (K * C)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
  have h1 : ‖c n‖ * ‖q‖ ^ n ≤ C * (‖q‖ / r) ^ n := by
    rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hr0 n)]
    calc ‖c n‖ * ‖q‖ ^ n * r ^ n = (‖c n‖ * r ^ n) * ‖q‖ ^ n := by ring
      _ ≤ C * ‖q‖ ^ n := by gcongr; exact hC n
  calc ‖d n‖ * ‖q‖ ^ n ≤ (K * (n : ℝ) ^ k * ‖c n‖) * ‖q‖ ^ n := by gcongr; exact hd n
    _ = K * (n : ℝ) ^ k * (‖c n‖ * ‖q‖ ^ n) := by ring
    _ ≤ K * (n : ℝ) ^ k * (C * (‖q‖ / r) ^ n) := by gcongr
    _ = K * C * ((n : ℝ) ^ k * (‖q‖ / r) ^ n) := by ring

/-- **Termwise differentiation** of a power series converging on the unit disc. -/
theorem hasDerivAt_pseries (c : ℕ → ℂ) (hc : ∀ q : ℂ, ‖q‖ < 1 → Summable (fun n => c n * q ^ n))
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w => ∑' n, c n * w ^ n) (∑' n, c n * ((n : ℂ) * z ^ (n - 1))) z := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hz
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr1
  have hrr : ‖(r : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]; exact hr2
  have hs := pseries_summable_norm c (fun n => (n : ℂ) * c n) hc 1 zero_le_one 1
    (fun n => by simp [norm_mul]) hrr
  have hu : Summable (fun n => ‖c n‖ * (n : ℝ) * r ^ (n - 1)) := by
    refine (hs.mul_left r⁻¹).congr fun n => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_mul, Complex.norm_natCast]
    rcases n with _ | n
    · simp
    · rw [pow_succ]; field_simp; simp
  refine hasDerivAt_tsum_of_isPreconnected (g := fun n w => c n * w ^ n)
    (g' := fun n w => c n * ((n : ℂ) * w ^ (n - 1))) hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected (fun n y _ => (hasDerivAt_pow n y).const_mul (c n))
    (fun n y hy => ?_) (Metric.mem_ball_self hr0) (hc 0 (by simp)) (by simpa using hr1)
  rw [Metric.mem_ball, dist_zero_right] at hy
  rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, ← mul_assoc]
  gcongr

end PSeries

/-! ## The derivative of the Eichler integral -/

section EichlerDeriv

variable {N : ℕ} [NeZero N] (f : Newform N 2)

theorem eCoeff_summable (q : ℂ) (hq : ‖q‖ < 1) : Summable (fun n => eCoeff f n * q ^ n) := by
  have hs := (eSeries f).hasSum (eSeries_mem_ball f hq)
  simp only [eSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hs
  exact hs.summable

theorem eSum_eq_tsum (q : ℂ) : (eSeries f).sum q = ∑' n, eCoeff f n * q ^ n := by
  rw [eSeries, ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  simp

theorem hasDerivAt_qC (w : ℂ) : HasDerivAt qC (2 * Real.pi * Complex.I * qC w) w := by
  unfold qC
  have := ((hasDerivAt_id w).const_mul (2 * Real.pi * Complex.I)).cexp
  simpa [mul_comm] using this

theorem hasDerivAt_eichler (τ : UpperHalfPlane) :
    HasDerivAt (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex)
      (2 * Real.pi * Complex.I * f.toCuspForm τ) τ := by
  have hq := norm_qC_lt_one τ.im_pos
  have h1 := (hasDerivAt_pseries (eCoeff f) (eCoeff_summable f) hq).comp (τ : ℂ) (hasDerivAt_qC τ)
  have hev : (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (τ : ℂ)]
      ((fun w => ∑' n, eCoeff f n * w ^ n) ∘ qC) := by
    filter_upwards [eichler_ofComplex_eventuallyEq f τ] with w hw
    rw [hw, Function.comp_apply, eSum_eq_tsum]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  convert h1 using 1
  have key : ∀ n : ℕ, eCoeff f n * ((n : ℂ) * qC τ ^ (n - 1)) * (2 * Real.pi * Complex.I * qC τ) =
      2 * Real.pi * Complex.I * (ZInQ.GZDecomp.coeff f n * qC τ ^ n) := by
    intro n
    rcases n with _ | n
    · simp [eCoeff, coeff_zero_newform]
    · simp only [eCoeff, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      rw [pow_succ]
      field_simp
  show _ = (∑' n, eCoeff f n * ((n : ℂ) * qC τ ^ (n - 1))) * (2 * Real.pi * Complex.I * qC τ)
  rw [← tsum_mul_right, funext key, tsum_mul_left, (hasSum_newform f τ).tsum_eq]

theorem mdiff_eichler : MDiff (ZInQ.GZHL3.eichler f) := fun τ =>
  UpperHalfPlane.mdifferentiableAt_iff.2 (hasDerivAt_eichler f τ).differentiableAt

theorem D_eichler : Derivative.normalizedDerivOfComplex (ZInQ.GZHL3.eichler f) = ⇑f.toCuspForm := by
  funext τ
  rw [Derivative.normalizedDerivOfComplex, (hasDerivAt_eichler f τ).deriv]
  field_simp

end EichlerDeriv

/-! ## The Eichler integral at the other cusps -/

section Cusp

variable {N : ℕ} [NeZero N] (f : Newform N 2)

theorem conj_T_mem_Gamma1 (γ : SL(2, ℤ)) :
    γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma1 N := by
  have hT : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simp only [CongruenceSubgroup.Gamma_mem, ModularGroup.coe_T_zpow]
    simp
  have h := (CongruenceSubgroup.Gamma_normal (N := N)).conj_mem _ hT γ
  rw [CongruenceSubgroup.Gamma_mem] at h
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨h.1, h.2.2.2, h.2.2.1⟩

/-- `f|₂γ`. -/
def fSlash (γ : SL(2, ℤ)) : UpperHalfPlane → ℂ := (⇑f.toCuspForm) ∣[(2 : ℤ)] γ

theorem fSlash_T (γ : SL(2, ℤ)) :
    fSlash f γ ∣[(2 : ℤ)] (ModularGroup.T ^ (N : ℤ)) = fSlash f γ := by
  unfold fSlash
  rw [← SlashAction.slash_mul]
  have e : γ * ModularGroup.T ^ (N : ℤ) = (γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹) * γ := by group
  rw [e, SlashAction.slash_mul]
  congr 1
  rw [ModularForm.SL_slash]
  exact f.toCuspForm.slash_action_eq' _ (Subgroup.mem_map_of_mem _ (conj_T_mem_Gamma1 γ))

theorem fSlash_periodic (γ : SL(2, ℤ)) :
    Function.Periodic (fSlash f γ ∘ UpperHalfPlane.ofComplex) (N : ℝ) := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + ((N : ℝ) : ℂ)).im := by simpa using hw
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    have h := congrFun (fSlash_T f γ) ⟨w, hw⟩
    rw [ModularForm.SL_slash_apply] at h
    have h10 : ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) 1 0) = 0 := by
      rw [show ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) 1 0) = (ModularGroup.T ^ (N : ℤ)).1 1 0 from rfl,
        ModularGroup.coe_T_zpow]; simp
    have h11 : ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) 1 1) = 1 := by
      rw [show ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) 1 1) = (ModularGroup.T ^ (N : ℤ)).1 1 1 from rfl,
        ModularGroup.coe_T_zpow]; simp
    have hd : UpperHalfPlane.denom (ModularGroup.T ^ (N : ℤ) : SL(2, ℤ))
        (⟨w, hw⟩ : UpperHalfPlane) = 1 := by
      rw [ModularGroup.denom_apply, h10, h11]; simp
    rw [hd, one_zpow, mul_one] at h
    rw [← h]
    congr 1
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_T_zpow_smul]
    simp [add_comm]
  · have hw' : ¬ 0 < (w + ((N : ℝ) : ℂ)).im := by simpa using hw
    simp only [Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.1 hw),
      UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.1 hw')]

theorem fSlash_mdiff (γ : SL(2, ℤ)) : MDiff (fSlash f γ) := by
  unfold fSlash
  rw [ModularForm.SL_slash]
  exact (ModularFormClass.holo f.toCuspForm).slash _ _

theorem fSlash_zero (γ : SL(2, ℤ)) : UpperHalfPlane.IsZeroAtImInfty (fSlash f γ) :=
  CuspFormClass.zero_at_infty_slash f.toCuspForm γ

theorem hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

/-- The `q_N`-expansion coefficients of `f|₂γ`. -/
def bCoeff (γ : SL(2, ℤ)) (m : ℕ) : ℂ := (UpperHalfPlane.qExpansion (N : ℝ) (fSlash f γ)).coeff m

theorem hasSum_fSlash (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    HasSum (fun m => bCoeff f γ m * Function.Periodic.qParam (N : ℝ) τ ^ m) (fSlash f γ τ) := by
  simpa [smul_eq_mul, bCoeff] using UpperHalfPlane.hasSum_qExpansion (hNpos (N := N))
    (fSlash_periodic f γ) (fSlash_mdiff f γ) (fSlash_zero f γ).isBoundedAtImInfty τ

theorem bCoeff_summable (γ : SL(2, ℤ)) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun m => bCoeff f γ m * q ^ m) := by
  simpa [smul_eq_mul, bCoeff] using (UpperHalfPlane.hasSum_qExpansion_of_norm_lt (hNpos (N := N))
    (fSlash_periodic f γ) (fSlash_mdiff f γ) (fSlash_zero f γ).isBoundedAtImInfty hq).summable

theorem bCoeff_zero (γ : SL(2, ℤ)) : bCoeff f γ 0 = 0 := by
  rw [bCoeff, UpperHalfPlane.qExpansion_coeff_zero (hNpos (N := N))
    (UpperHalfPlane.analyticAt_cuspFunction_zero (hNpos (N := N)) (fSlash_periodic f γ)
      (fSlash_mdiff f γ) (fSlash_zero f γ).isBoundedAtImInfty) (fSlash_periodic f γ)]
  exact (fSlash_zero f γ).valueAtInfty_eq_zero

/-- The coefficients of the antiderivative `Σ_{m ≥ 1} b_m (N/m) q_N^m`. -/
def betaC (γ : SL(2, ℤ)) (m : ℕ) : ℂ := if m = 0 then 0 else bCoeff f γ m * N / m

theorem betaC_norm (γ : SL(2, ℤ)) (m : ℕ) : ‖betaC f γ m‖ ≤ N * (m : ℝ) ^ 0 * ‖bCoeff f γ m‖ := by
  unfold betaC
  split_ifs with hm
  · simp only [norm_zero, pow_zero, mul_one]; positivity
  · rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast, pow_zero, mul_one]
    have h1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ N * ‖bCoeff f γ m‖)
    linarith

theorem betaC_summable_norm (γ : SL(2, ℤ)) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun m => ‖betaC f γ m‖ * ‖q‖ ^ m) :=
  pseries_summable_norm (bCoeff f γ) (betaC f γ) (bCoeff_summable f γ) N (by positivity) 0
    (betaC_norm f γ) hq

theorem betaC_summable (γ : SL(2, ℤ)) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun m => betaC f γ m * q ^ m) :=
  Summable.of_norm ((betaC_summable_norm f γ hq).congr fun m => by rw [norm_mul, norm_pow])

/-- `G(τ) = Σ_{m ≥ 1} b_m (N/m) q_N(τ)^m`. -/
def Gq (γ : SL(2, ℤ)) (τ : UpperHalfPlane) : ℂ :=
  ∑' m, betaC f γ m * Function.Periodic.qParam (N : ℝ) τ ^ m

theorem hasDerivAt_qParamN (w : ℂ) :
    HasDerivAt (fun w => Function.Periodic.qParam (N : ℝ) w)
      (2 * Real.pi * Complex.I / N * Function.Periodic.qParam (N : ℝ) w) w := by
  have := ((hasDerivAt_id w).const_mul (2 * Real.pi * Complex.I / (N : ℂ))).cexp
  convert this using 1
  · funext z; simp [Function.Periodic.qParam]; ring_nf
  · simp [Function.Periodic.qParam]; ring_nf

theorem hasDerivAt_Gq (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    HasDerivAt (Gq f γ ∘ UpperHalfPlane.ofComplex)
      (2 * Real.pi * Complex.I * fSlash f γ τ) τ := by
  have hq : ‖Function.Periodic.qParam (N : ℝ) (τ : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one (hNpos (N := N)) τ.im_pos
  have h1 := (hasDerivAt_pseries (betaC f γ) (betaC_summable f γ) hq).comp (τ : ℂ)
    (hasDerivAt_qParamN (N := N) τ)
  have hev : (Gq f γ ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (τ : ℂ)]
      ((fun w => ∑' m, betaC f γ m * w ^ m) ∘ fun w => Function.Periodic.qParam (N : ℝ) w) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
    simp only [Function.comp_apply, Gq, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  convert h1 using 1
  set q := Function.Periodic.qParam (N : ℝ) (τ : ℂ)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have key : ∀ m : ℕ, betaC f γ m * ((m : ℂ) * q ^ (m - 1)) * (2 * Real.pi * Complex.I / N * q) =
      2 * Real.pi * Complex.I * (bCoeff f γ m * q ^ m) := by
    intro m
    rcases m with _ | m
    · simp [betaC, bCoeff_zero]
    · simp only [betaC, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]
      have hm : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      rw [pow_succ]
      field_simp
  show _ = (∑' m, betaC f γ m * ((m : ℂ) * q ^ (m - 1))) * (2 * Real.pi * Complex.I / N * q)
  rw [← tsum_mul_right, funext key, tsum_mul_left, (hasSum_fSlash f γ τ).tsum_eq]

theorem mdiff_Gq (γ : SL(2, ℤ)) : MDiff (Gq f γ) := fun τ =>
  UpperHalfPlane.mdifferentiableAt_iff.2 (hasDerivAt_Gq f γ τ).differentiableAt

theorem D_Gq (γ : SL(2, ℤ)) : Derivative.normalizedDerivOfComplex (Gq f γ) = fSlash f γ := by
  funext τ
  rw [Derivative.normalizedDerivOfComplex, (hasDerivAt_Gq f γ τ).deriv]
  field_simp

theorem eichler_slash (γ : SL(2, ℤ)) :
    (ZInQ.GZHL3.eichler f ∣[(0 : ℤ)] γ) = fun τ => ZInQ.GZHL3.eichler f (γ • τ) := by
  funext τ
  rw [ModularForm.SL_slash_apply]
  simp

theorem D_eichler_slash (γ : SL(2, ℤ)) :
    Derivative.normalizedDerivOfComplex (fun τ => ZInQ.GZHL3.eichler f (γ • τ)) = fSlash f γ := by
  rw [← eichler_slash, Derivative.normalizedDerivOfComplex_SL_slash (mdiff_eichler f), D_eichler]
  funext τ
  simp [fSlash]

theorem mdiff_eichler_slash (γ : SL(2, ℤ)) : MDiff (fun τ => ZInQ.GZHL3.eichler f (γ • τ)) := by
  rw [← eichler_slash, ModularForm.SL_slash]
  exact (mdiff_eichler f).slash _ _

/-- **`φ_f(γτ) = K₀ + Σ_{m ≥ 1} b_m (N/m) q_N^m`**: the Eichler integral is holomorphic at every
cusp. -/
theorem exists_const_eichler (γ : SL(2, ℤ)) :
    ∃ K₀ : ℂ, ∀ τ : UpperHalfPlane, ZInQ.GZHL3.eichler f (γ • τ) = K₀ + Gq f γ τ := by
  set H : UpperHalfPlane → ℂ := fun τ => ZInQ.GZHL3.eichler f (γ • τ) - Gq f γ τ with hH
  have hmd : MDiff H := (mdiff_eichler_slash f γ).sub (mdiff_Gq f γ)
  have hD : Derivative.normalizedDerivOfComplex H = 0 := by
    rw [hH, show (fun τ => ZInQ.GZHL3.eichler f (γ • τ) - Gq f γ τ) =
      (fun τ => ZInQ.GZHL3.eichler f (γ • τ)) - Gq f γ from rfl,
      Derivative.normalizedDerivOfComplex_sub _ _ (mdiff_eichler_slash f γ) (mdiff_Gq f γ),
      D_eichler_slash, D_Gq, sub_self]
  have hderiv : Set.EqOn (deriv (H ∘ UpperHalfPlane.ofComplex)) 0 {z : ℂ | 0 < z.im} := by
    intro w hw
    have h := congrFun hD ⟨w, hw⟩
    simp only [Derivative.normalizedDerivOfComplex, Pi.zero_apply] at h
    have h2 : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    exact (mul_eq_zero.1 h).resolve_left h2
  obtain ⟨a, ha⟩ := UpperHalfPlane.isOpen_upperHalfPlaneSet.exists_is_const_of_deriv_eq_zero
    (convex_halfSpace_im_gt 0).isPreconnected (UpperHalfPlane.mdifferentiable_iff.1 hmd) hderiv
  refine ⟨a, fun τ => ?_⟩
  have := ha τ τ.im_pos
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] at this
  rw [← this]; simp [hH]

/-- The antiderivative as a power series sum (analytic at `q = 0`). -/
def Gser (γ : SL(2, ℤ)) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (betaC f γ)

theorem Gser_radius (γ : SL(2, ℤ)) : 0 < (Gser f γ).radius := by
  have h := (Gser f γ).le_radius_of_summable_norm (r := (1 / 2 : NNReal)) (by
    have := betaC_summable_norm f γ (q := (1 / 2 : ℂ)) (by norm_num)
    refine this.congr fun m => ?_
    rw [Gser, FormalMultilinearSeries.ofScalars_norm]
    norm_num)
  exact lt_of_lt_of_le (by norm_num) h

theorem Gq_eq (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    Gq f γ τ = (Gser f γ).sum (Function.Periodic.qParam (N : ℝ) τ) := by
  rw [Gser, ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  simp [Gq]

theorem analyticAt_Gser (γ : SL(2, ℤ)) : AnalyticAt ℂ (Gser f γ).sum 0 :=
  ((Gser f γ).hasFPowerSeriesOnBall (Gser_radius f γ)).analyticAt_of_mem
    (by rw [Metric.mem_eball, edist_self]; exact Gser_radius f γ)

end Cusp

/-- **Moderate growth from meromorphy at the cusp.** If `F(τ) = M(q_N(τ))` with `M` meromorphic at
`q = 0`, then `F(τ) = O(e^{2πk Im τ})` as `Im τ → ∞`. -/
theorem growth_of_meromorphicAt {N : ℕ} [NeZero N] {M : ℂ → ℂ} (hM : MeromorphicAt M 0)
    (F : UpperHalfPlane → ℂ) (hF : ∀ τ, F τ = M (Function.Periodic.qParam (N : ℝ) τ)) :
    ∃ k : ℕ, F =O[UpperHalfPlane.atImInfty] fun τ => Real.exp (2 * Real.pi * k * τ.im) := by
  obtain ⟨n, hn⟩ := hM
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 hn.continuousAt 1 one_pos
  set C : ℝ := ‖(fun z => (z - 0) ^ n • M z) 0‖ + 1
  have hNpos' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨n, Asymptotics.IsBigO.of_bound C ?_⟩
  rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem]
  refine ⟨N * |Real.log δ| / (2 * Real.pi) + 1, fun τ hτ => ?_⟩
  simp only [Set.mem_setOf_eq]
  set q := Function.Periodic.qParam (N : ℝ) (τ : ℂ)
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hqn : ‖q‖ = Real.exp (-2 * Real.pi * τ.im / N) := by
    rw [Function.Periodic.norm_qParam (N : ℝ) (τ : ℂ)]; rfl
  have hqδ : ‖q‖ < δ := by
    rw [hqn]
    have hπ := Real.pi_pos
    have h1 : -2 * Real.pi * τ.im / N < Real.log δ := by
      have hA : N * |Real.log δ| / (2 * Real.pi) < τ.im := by linarith [hτ]
      rw [div_lt_iff₀ (by positivity) ] at hA
      have : -2 * Real.pi * τ.im / N < -|Real.log δ| := by
        rw [div_lt_iff₀ hNpos']; nlinarith
      linarith [neg_abs_le (Real.log δ)]
    calc Real.exp (-2 * Real.pi * τ.im / N) < Real.exp (Real.log δ) := Real.exp_lt_exp.2 h1
      _ = δ := Real.exp_log hδ
  have hb := hδb (x := q) (by rw [dist_zero_right]; exact hqδ)
  rw [dist_eq_norm] at hb
  have hb' : ‖(q - 0) ^ n • M q‖ ≤ C := by
    have := norm_sub_norm_le ((fun z => (z - 0) ^ n • M z) q) ((fun z => (z - 0) ^ n • M z) 0)
    simp only at this; linarith
  rw [sub_zero, norm_smul, norm_pow] at hb'
  have hqpos : 0 < ‖q‖ := norm_pos_iff.2 hq0
  rw [hF τ, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hM' : ‖M q‖ ≤ C / ‖q‖ ^ n := by
    rw [le_div_iff₀ (pow_pos hqpos n)]; linarith [mul_comm (‖q‖ ^ n) ‖M q‖]
  refine hM'.trans ?_
  rw [div_le_iff₀ (pow_pos hqpos n), hqn, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  have hC : 0 ≤ C := by positivity
  have h2 : 2 * Real.pi * n * τ.im + n * (-2 * Real.pi * τ.im / N) ≥ 0 := by
    have hτ0 : 0 < τ.im := τ.im_pos
    have h3 : n * (2 * Real.pi * τ.im / N) ≤ n * (2 * Real.pi * τ.im) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      rw [div_le_iff₀ hNpos']
      have : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
      nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hτ0.le)
        (sub_nonneg.2 this)]
    have : n * (-2 * Real.pi * τ.im / N) = -(n * (2 * Real.pi * τ.im / N)) := by ring
    rw [this]; nlinarith
  calc C = C * 1 := (mul_one C).symm
    _ ≤ C * Real.exp (2 * Real.pi * n * τ.im + n * (-2 * Real.pi * τ.im / N)) := by
        gcongr; exact Real.one_le_exp h2


/-- **(GLUE, analysis; proved: `paramCuspGrowth`) Moderate growth of the coordinates of `φ` at every
cusp.** For `γ ∈ SL₂(ℤ)`, each of `x(φ(γτ))`, `y(φ(γτ))`, `1/(x(φ(γτ)) − t)` is `O(e^{2πk Im τ})` as
`Im τ → ∞`, for some `k`. -/
def ParamCuspGrowth : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2)
    (L : PeriodPair) (c : ℚ), ParamSetting E f L c → ∀ γ : SL(2, ℤ),
    (∃ k : ℕ, (fun τ : UpperHalfPlane => xPar E L f c (γ • τ)) =O[UpperHalfPlane.atImInfty]
        (fun τ => Real.exp (2 * Real.pi * k * τ.im))) ∧
    (∃ k : ℕ, (fun τ : UpperHalfPlane => yPar E L f c (γ • τ)) =O[UpperHalfPlane.atImInfty]
        (fun τ => Real.exp (2 * Real.pi * k * τ.im))) ∧
    ∀ t : ℚ, ∃ k : ℕ, (fun τ : UpperHalfPlane => gPar E L f c t (γ • τ)) =O[UpperHalfPlane.atImInfty]
        (fun τ => Real.exp (2 * Real.pi * k * τ.im))

theorem meromorphicAt_wpb (L : PeriodPair) (b z₀ : ℂ) :
    MeromorphicAt (fun z => L.weierstrassP z - b) z₀ :=
  (meromorphicAt_wp L z₀).sub (MeromorphicAt.const _ _)

theorem meromorphicAt_psi (L : PeriodPair) (a₁ a₃ b z₀ : ℂ) :
    MeromorphicAt (fun z => (L.derivWeierstrassP z - a₁ * (L.weierstrassP z - b) - a₃) / 2) z₀ :=
  (((meromorphicAt_dwp L z₀).sub ((MeromorphicAt.const _ _).mul (meromorphicAt_wpb L b z₀))).sub
    (MeromorphicAt.const _ _)).div (MeromorphicAt.const _ _)

/-- **`ParamCuspGrowth`, proved.** -/
theorem paramCuspGrowth : ParamCuspGrowth := by
  intro E _ N _ f L c _ γ
  obtain ⟨K₀, hK⟩ := exists_const_eichler f γ
  set Z : ℂ → ℂ := fun q => (c : ℂ) * K₀ + (c : ℂ) * (Gser f γ).sum q with hZdef
  have hZ : AnalyticAt ℂ Z 0 := analyticAt_const.add (analyticAt_const.mul (analyticAt_Gser f γ))
  have hz : ∀ τ : UpperHalfPlane, zPar f c (γ • τ) = Z (Function.Periodic.qParam (N : ℝ) τ) := by
    intro τ; simp only [zPar, hK, Gq_eq, hZdef]; ring
  set b : ℂ := (E⁄ℂ).b₂ / 12 with hb
  refine ⟨growth_of_meromorphicAt (N := N) ((meromorphicAt_wpb L b _).comp_analyticAt hZ) _
      (fun τ => by simp only [xPar, hz, Function.comp_apply, hb]),
    growth_of_meromorphicAt (N := N)
      ((meromorphicAt_psi L (E⁄ℂ).a₁ (E⁄ℂ).a₃ b _).comp_analyticAt hZ) _
      (fun τ => by simp only [yPar, xPar, hz, Function.comp_apply, hb]),
    fun t => growth_of_meromorphicAt (N := N) ((meromorphicAt_phiT L (b + t) _).comp_analyticAt hZ)
      _ (fun τ => by
        show gPar E L f c t (γ • τ) = phiT L (b + t) (Z (Function.Periodic.qParam (N : ℝ) τ))
        unfold gPar phiT xPar
        rw [hz τ, sub_sub])⟩

/-! ## Taylor series at `0` as power series; the Weierstrass equation in `q` -/

section Taylor

open PowerSeries Nat

/-- The Taylor series of `f` at `0`. -/
def tay (f : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk fun n => ((n ! : ℂ))⁻¹ * iteratedDeriv n f 0

theorem coeff_tay (f : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (tay f) = ((n ! : ℂ))⁻¹ * iteratedDeriv n f 0 := by
  simp [tay]

theorem tay_congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) : tay f = tay g := by
  ext n; rw [coeff_tay, coeff_tay, h.iteratedDeriv_eq n]

theorem tay_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun w => f w + g w) = tay f + tay g := by
  ext n
  rw [coeff_tay, map_add, coeff_tay, coeff_tay,
    iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt]
  ring

theorem tay_sub {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun w => f w - g w) = tay f - tay g := by
  ext n
  rw [coeff_tay, map_sub, coeff_tay, coeff_tay,
    iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt]
  ring

theorem tay_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun w => f w * g w) = tay f * tay g := by
  ext n
  rw [coeff_tay, iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [coeff_tay, coeff_tay]
  have hkn : k ≤ n := Nat.lt_succ_iff.1 hk
  have h := Nat.choose_mul_factorial_mul_factorial hkn
  have h1 : ((n ! : ℂ)) = (n.choose k : ℂ) * (k ! : ℂ) * ((n - k) ! : ℂ) := by exact_mod_cast h.symm
  have hk0 : ((k ! : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnk0 : (((n - k) ! : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
  have hc0 : ((n.choose k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
  rw [h1]
  field_simp

theorem tay_const (c : ℂ) : tay (fun _ => c) = PowerSeries.C c := by
  ext n
  rw [coeff_tay, iteratedDeriv_const, PowerSeries.coeff_C]
  split_ifs <;> simp_all

theorem tay_id : tay (fun w => w) = PowerSeries.X := by
  ext n
  rw [coeff_tay, iteratedDeriv_fun_id_zero, PowerSeries.coeff_X]
  split_ifs with h <;> simp [h]

theorem tay_deriv {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) : tay (deriv f) = d⁄dX (tay f) := by
  ext n
  rw [coeff_tay, PowerSeries.coeff_derivative, coeff_tay, ← iteratedDeriv_succ']
  rw [Nat.factorial_succ]
  push_cast
  have : ((n ! : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

/-- The Weierstrass equation for `Y = w²(℘(Z(w)) − b)` as a formal power series identity:
`(wY' − 2Y)² = (4(Y + bw²)³ − g₂w⁴(Y + bw²) − g₃w⁶)·A`. -/
def odePhi (A : ℂ⟦X⟧) (b g₂ g₃ : ℂ) (S : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  (X * d⁄dX S - 2 * S) ^ 2 -
    (4 * (S + C b * X ^ 2) ^ 3 - C g₂ * X ^ 4 * (S + C b * X ^ 2) - C g₃ * X ^ 6) * A

theorem X_mul_derivative_X_pow_mul (n : ℕ) (ε : ℂ⟦X⟧) :
    X * d⁄dX (X ^ n * ε) = X ^ n * (C (n : ℂ) * ε + X * d⁄dX ε) := by
  rw [Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_X, smul_eq_mul,
    smul_eq_mul]
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel, pow_succ, map_natCast]
    push_cast
    ring

/-- **Uniqueness of the formal solution with given constant term.** -/
theorem odePhi_unique (A : ℂ⟦X⟧) (b g₂ g₃ : ℂ) {S T : ℂ⟦X⟧} (hS : odePhi A b g₂ g₃ S = 0)
    (hT : odePhi A b g₂ g₃ T = 0) (h0 : constantCoeff S = constantCoeff T)
    (hne : constantCoeff S ≠ 0) (hA : constantCoeff A * constantCoeff S = 1) : S = T := by
  suffices h : ∀ n, ∀ m < n, PowerSeries.coeff m S = PowerSeries.coeff m T by
    ext m; exact h (m + 1) m (Nat.lt_succ_self m)
  intro n
  induction n with
  | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
  | succ n ih =>
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · exact ih m hm
    obtain ⟨ε, hε⟩ : X ^ m ∣ S - T := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro k hk; rw [map_sub, ih k hk, sub_self]
    have hSe : S = T + X ^ m * ε := by rw [← hε]; ring
    have hdS : X * d⁄dX S = X * d⁄dX T + X ^ m * (C (m : ℂ) * ε + X * d⁄dX ε) := by
      rw [hSe, map_add, mul_add, X_mul_derivative_X_pow_mul]
    have key : odePhi A b g₂ g₃ S - odePhi A b g₂ g₃ T = X ^ m *
        ((X * d⁄dX T + X ^ m * (C (m : ℂ) * ε + X * d⁄dX ε) - 2 * S + (X * d⁄dX T - 2 * T)) *
          (C (m : ℂ) * ε + X * d⁄dX ε - 2 * ε) -
        A * (4 * ((S + C b * X ^ 2) ^ 2 + (S + C b * X ^ 2) * (T + C b * X ^ 2) +
          (T + C b * X ^ 2) ^ 2) - C g₂ * X ^ 4) * ε) := by
      unfold odePhi
      rw [hdS, hSe]
      ring
    set B := (X * d⁄dX T + X ^ m * (C (m : ℂ) * ε + X * d⁄dX ε) - 2 * S + (X * d⁄dX T - 2 * T)) *
          (C (m : ℂ) * ε + X * d⁄dX ε - 2 * ε) -
        A * (4 * ((S + C b * X ^ 2) ^ 2 + (S + C b * X ^ 2) * (T + C b * X ^ 2) +
          (T + C b * X ^ 2) ^ 2) - C g₂ * X ^ 4) * ε with hBdef
    rw [hS, hT, sub_zero] at key
    have hB : B = 0 := (mul_eq_zero.1 key.symm).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)
    have hc := congrArg constantCoeff hB
    have hX0 : constantCoeff (X : ℂ⟦X⟧) = 0 := PowerSeries.constantCoeff_X
    simp only [hBdef, map_sub, map_add, map_mul, map_pow, hX0, PowerSeries.constantCoeff_C,
      map_ofNat, zero_mul, mul_zero, zero_pow (two_ne_zero), zero_add, add_zero, sub_zero,
      map_zero] at hc
    rw [← h0] at hc
    set s₀ := constantCoeff S
    set e₀ := constantCoeff ε
    have hz : (0 : ℂ) ^ m * (m : ℂ) = 0 := by rcases m with _ | m <;> simp
    have hc' : -4 * s₀ * e₀ * ((m : ℂ) - 2 + 3 * (constantCoeff A * s₀)) = 0 := by
      linear_combination hc + e₀ ^ 2 * (2 - (m : ℂ)) * hz
    rw [hA] at hc'
    have hm1 : ((m : ℂ) - 2 + 3 * 1) ≠ 0 := by
      have : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      convert this using 1; ring
    have he : e₀ = 0 := by
      rcases mul_eq_zero.1 hc' with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exfalso; apply hne; have : (-4 : ℂ) ≠ 0 := by norm_num
          exact (mul_eq_zero.1 h).resolve_left this
        · exact h
      · exact absurd h hm1
    have : PowerSeries.coeff m (S - T) = 0 := by
      rw [hε, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact he
    rw [map_sub, sub_eq_zero] at this
    exact this

theorem map_derivative (σ : ℂ →+* ℂ) (S : ℂ⟦X⟧) :
    PowerSeries.map σ (d⁄dX S) = d⁄dX (PowerSeries.map σ S) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
    PowerSeries.coeff_map, map_mul]
  simp

theorem map_odePhi (σ : ℂ →+* ℂ) (A : ℂ⟦X⟧) (b g₂ g₃ : ℂ) (S : ℂ⟦X⟧) :
    PowerSeries.map σ (odePhi A b g₂ g₃ S) =
      odePhi (PowerSeries.map σ A) (σ b) (σ g₂) (σ g₃) (PowerSeries.map σ S) := by
  simp only [odePhi, map_sub, map_mul, map_pow, map_add, PowerSeries.map_X, PowerSeries.map_C,
    map_derivative, map_ofNat]

/-- **The fixed field of `Aut(ℂ)` is `ℚ`.** -/
theorem rat_of_fixed (z : ℂ) (hz : ∀ σ : ℂ ≃+* ℂ, σ z = z) : ∃ q : ℚ, (q : ℂ) = z := by
  obtain ⟨a, ha⟩ := T5Glue.fixedAlgebraic z (fun σ _ => hz σ)
  have hfix : ∀ ρ : Qbar ≃ₐ[ℚ] Qbar, ρ a = a := by
    intro ρ
    obtain ⟨σ, hσ⟩ := T5Glue.autExtends ρ
    apply ιC.injective
    rw [← hσ, ha, hz]
  obtain ⟨q, hq⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed a).2 hfix
  exact ⟨q, by rw [← ha, ← hq]; simp⟩

end Taylor

/-! ## The `q`-expansion of `x∘φ` at `∞` -/

section QExp

open PowerSeries

variable {N : ℕ} [NeZero N] (f : Newform N 2)

/-- `V(w) = Σ e_{n+1} wⁿ`, so that `φ_f = q·V(q)`. -/
def vSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => eCoeff f (n + 1))

def vFun : ℂ → ℂ := (vSeries f).sum

theorem vCoeff_summable (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n => eCoeff f (n + 1) * q ^ n) := by
  have h := (summable_nat_add_iff 1).2 (eCoeff_summable f q hq)
  by_cases h0 : q = 0
  · subst h0; exact summable_of_ne_finset_zero (s := {0}) (fun n hn => by
      simp at hn; simp [hn])
  · refine (h.mul_left q⁻¹).congr fun n => ?_
    rw [pow_succ]; field_simp

theorem vSeries_le_radius (r : NNReal) (hr : (r : ℝ) < 1) : (r : ENNReal) ≤ (vSeries f).radius := by
  apply (vSeries f).le_radius_of_tendsto (l := 0)
  have hr' : ‖((r : ℝ) : ℂ)‖ < 1 := by simpa using hr
  have ht := (vCoeff_summable f ((r : ℝ) : ℂ) hr').tendsto_atTop_zero.norm
  simp only [norm_zero] at ht
  refine ht.congr fun n => ?_
  simp [vSeries, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow]

theorem vSeries_mem_ball {w : ℂ} (hw : ‖w‖ < 1) : w ∈ Metric.eball (0 : ℂ) (vSeries f).radius := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hw
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr1.le
  set r' : NNReal := ⟨r, hr0⟩
  rw [Metric.mem_eball, edist_zero_right]
  calc (‖w‖₊ : ENNReal) < (r' : ENNReal) := by rw [ENNReal.coe_lt_coe]; exact_mod_cast hr1
    _ ≤ _ := vSeries_le_radius f r' hr2

theorem vSeries_radius_pos : 0 < (vSeries f).radius := by
  have := vSeries_mem_ball f (w := 0) (by simp)
  rw [Metric.mem_eball] at this; exact lt_of_le_of_lt bot_le this

theorem vFun_hasFPS : HasFPowerSeriesOnBall (vFun f) (vSeries f) 0 (vSeries f).radius :=
  (vSeries f).hasFPowerSeriesOnBall (vSeries_radius_pos f)

theorem analyticAt_vFun : AnalyticAt ℂ (vFun f) 0 := (vFun_hasFPS f).analyticAt

theorem vFun_eq (q : ℂ) (hq : ‖q‖ < 1) : vFun f q = ∑' n, eCoeff f (n + 1) * q ^ n := by
  have hs := (vSeries f).hasSum (vSeries_mem_ball f hq)
  simp only [vSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hs
  exact hs.tsum_eq.symm

theorem eSum_eq_mul_vFun (q : ℂ) (hq : ‖q‖ < 1) : (eSeries f).sum q = q * vFun f q := by
  rw [eSum_eq_tsum, vFun_eq f q hq, ← tsum_mul_left,
    (eCoeff_summable f q hq).tsum_eq_zero_add]
  have h0 : eCoeff f 0 = 0 := by simp [eCoeff]
  rw [h0, zero_mul, zero_add]
  congr 1; funext n; rw [pow_succ]; ring

theorem eCoeff_one : eCoeff f 1 = 1 := by
  simp only [eCoeff, one_ne_zero, if_false, Nat.cast_one, div_one]
  exact f.isNorm

theorem vFun_zero : vFun f 0 = 1 := by
  rw [vFun_eq f 0 (by simp), tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp [eCoeff_one]

theorem coeff_tay_vFun (n : ℕ) : PowerSeries.coeff n (tay (vFun f)) = eCoeff f (n + 1) := by
  rw [coeff_tay]
  have h := (vFun_hasFPS f).factorial_smul 1 n
  rw [iteratedDeriv_eq_iteratedFDeriv, ← h]
  simp only [vSeries, FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one,
    nsmul_eq_mul]
  have : ((n.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

variable (L : PeriodPair)

/-- `Z(w) = c·w·V(w)` (`= c φ_f` at `w = q`). -/
def zF (c : ℂ) (w : ℂ) : ℂ := c * w * vFun f w

/-- `Ŷ(w) = w²℘_{L−0}(Z(w)) + (c²V(w)²)⁻¹ − b w²` (`= w²(℘(Z(w)) − b)` for `w ≠ 0`). -/
def yF (c b : ℂ) (w : ℂ) : ℂ :=
  w ^ 2 * L.weierstrassPExcept 0 (zF f c w) + (c ^ 2 * vFun f w ^ 2)⁻¹ - b * w ^ 2

theorem analyticAt_vFun_of {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ (vFun f) w :=
  (vFun_hasFPS f).analyticAt_of_mem (vSeries_mem_ball f hw)

theorem analyticAt_zF (c : ℂ) {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ (zF f c) w := by
  have := analyticAt_vFun_of f hw
  unfold zF; fun_prop

theorem zF_zero (c : ℂ) : zF f c 0 = 0 := by simp [zF]

theorem analyticAt_yF {c : ℂ} (hc : c ≠ 0) (b : ℂ) : AnalyticAt ℂ (yF f L c b) 0 := by
  have hV := analyticAt_vFun f
  have hE : AnalyticAt ℂ (fun w => L.weierstrassPExcept 0 (zF f c w)) 0 := by
    exact (L.analyticAt_weierstrassPExcept 0).comp_of_eq (analyticAt_zF f c (by simp))
      (zF_zero f c)
  have hden : AnalyticAt ℂ (fun w => c ^ 2 * vFun f w ^ 2) 0 := by fun_prop
  have hne : c ^ 2 * vFun f 0 ^ 2 ≠ 0 := by rw [vFun_zero]; simpa using hc
  unfold yF
  exact ((analyticAt_id.pow 2).mul hE).add (hden.inv hne) |>.sub (analyticAt_const.mul
    (analyticAt_id.pow 2))

theorem yF_zero (c b : ℂ) : yF f L c b 0 = (c ^ 2)⁻¹ := by simp [yF, vFun_zero]

/-- A punctured ball around `0` on which `V ≠ 0` and `Z(w) ∉ L`. -/
theorem exists_good_ball {c : ℂ} (hc : c ≠ 0) :
    ∃ ε > 0, ε ≤ 1 / 2 ∧ ∀ w : ℂ, ‖w‖ < ε → vFun f w ≠ 0 ∧ (w ≠ 0 → zF f c w ∉ L.lattice) := by
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 (analyticAt_vFun f).continuousAt (1 / 2)
    (by norm_num)
  obtain ⟨r, hr, hrb⟩ := Metric.mem_nhds_iff.1 (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  refine ⟨min (min δ (r / (2 * ‖c‖))) (1 / 2), by positivity, min_le_right _ _, fun w hw => ?_⟩
  have hw1 : ‖w‖ < δ := lt_of_lt_of_le hw ((min_le_left _ _).trans (min_le_left _ _))
  have hw2 : ‖w‖ < r / (2 * ‖c‖) := lt_of_lt_of_le hw ((min_le_left _ _).trans (min_le_right _ _))
  have hV := hδb (x := w) (by rwa [dist_zero_right])
  rw [dist_eq_norm, vFun_zero] at hV
  have hVne : vFun f w ≠ 0 := by
    intro h0; rw [h0, zero_sub, norm_neg, norm_one] at hV; norm_num at hV
  have hVle : ‖vFun f w‖ < 3 / 2 := by
    have := norm_le_norm_sub_add (vFun f w) 1
    rw [norm_one] at this; linarith
  refine ⟨hVne, fun hw0 hzL => ?_⟩
  have hz0 : zF f c w ≠ 0 := by
    unfold zF; exact mul_ne_zero (mul_ne_zero hc hw0) hVne
  have hzr : zF f c w ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, zF, norm_mul, norm_mul]
    calc ‖c‖ * ‖w‖ * ‖vFun f w‖ ≤ ‖c‖ * ‖w‖ * (3 / 2) := by gcongr
      _ < ‖c‖ * (r / (2 * ‖c‖)) * (3 / 2) := by gcongr
      _ = 3 / 4 * r := by field_simp; ring
      _ < r := by linarith
  exact hrb hzr ⟨hzL, hz0⟩

theorem yF_eq {c : ℂ} (hc : c ≠ 0) (b : ℂ) {w : ℂ} (hV : vFun f w ≠ 0) (hw : w ≠ 0) :
    yF f L c b w = w ^ 2 * (L.weierstrassP (zF f c w) - b) := by
  have h := L.weierstrassPExcept_add ⟨0, L.lattice.zero_mem⟩ (zF f c w)
  simp only [sub_zero, div_zero, one_div, zero_pow two_ne_zero, inv_zero] at h
  unfold yF
  rw [← h]
  simp only [zF]
  field_simp

theorem hasDerivAt_wp {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have hd := (analyticAt_wp L hz).differentiableAt.hasDerivAt
  rwa [L.deriv_weierstrassP] at hd

theorem constantCoeff_tay (f : ℂ → ℂ) : PowerSeries.constantCoeff (tay f) = f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_tay]; simp

theorem tay_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    tay (fun w => f w ^ n) = (tay f) ^ n := by
  induction n with
  | zero => simp only [pow_zero]; rw [tay_const]; rfl
  | succ n ih =>
    have e : (fun w => f w ^ (n + 1)) = fun w => f w ^ n * f w := by funext w; ring
    have h := tay_mul (f := fun w => f w ^ n) (g := f) (hf.pow n) hf
    beta_reduce at h
    rw [e, h, ih, pow_succ]

theorem tay_cmul (c : ℂ) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    tay (fun w => c * f w) = PowerSeries.C c * tay f := by
  rw [tay_mul analyticAt_const hf, tay_const]

theorem tay_X_pow (n : ℕ) : tay (fun w => w ^ n) = PowerSeries.X ^ n := by
  have := tay_pow (f := fun w => w) analyticAt_id n
  simpa [tay_id] using this

/-- On the punctured good ball: `wŶ' − 2Ŷ = w³ ℘'(Z(w)) Z'(w)`. -/
theorem yF_deriv_eq {c : ℂ} (hc : c ≠ 0) (b : ℂ) {ε : ℝ} (hε1 : ε ≤ 1 / 2)
    (hgood : ∀ w : ℂ, ‖w‖ < ε → vFun f w ≠ 0 ∧ (w ≠ 0 → zF f c w ∉ L.lattice)) {w : ℂ}
    (hw : ‖w‖ < ε) (hw0 : w ≠ 0) :
    w * deriv (yF f L c b) w - 2 * yF f L c b w =
      w ^ 3 * L.derivWeierstrassP (zF f c w) * deriv (zF f c) w := by
  obtain ⟨hV, hZL⟩ := hgood w hw
  have hzL := hZL hw0
  have hopen : IsOpen {v : ℂ | v ≠ 0 ∧ ‖v‖ < ε} :=
    isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
  have hev : yF f L c b =ᶠ[nhds w] fun v => v ^ 2 * (L.weierstrassP (zF f c v) - b) := by
    filter_upwards [hopen.mem_nhds ⟨hw0, hw⟩] with v hv
    exact yF_eq f L hc b (hgood v hv.2).1 hv.1
  have hZw : HasDerivAt (zF f c) (deriv (zF f c) w) w :=
    (analyticAt_zF f c (by linarith : ‖w‖ < 1)).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun v : ℂ => v ^ 2) (2 * w) w := by
    simpa using hasDerivAt_pow 2 w
  have hd : HasDerivAt (fun v => v ^ 2 * (L.weierstrassP (zF f c v) - b))
      (2 * w * (L.weierstrassP (zF f c w) - b) +
        w ^ 2 * (L.derivWeierstrassP (zF f c w) * deriv (zF f c) w)) w :=
    h1.mul (((hasDerivAt_wp L hzL).comp w hZw).sub_const b)
  rw [hev.deriv_eq, hd.deriv, yF_eq f L hc b hV hw0]
  ring

/-- **The Weierstrass equation in the variable `w`**, near `0`. -/
theorem yF_ode {c : ℂ} (hc : c ≠ 0) (b : ℂ) :
    (fun w => (w * deriv (yF f L c b) w - 2 * yF f L c b w) ^ 2) =ᶠ[nhds 0]
      fun w => (4 * (yF f L c b w + b * w ^ 2) ^ 3 - L.g₂ * w ^ 4 * (yF f L c b w + b * w ^ 2) -
        L.g₃ * w ^ 6) * deriv (zF f c) w ^ 2 := by
  obtain ⟨ε, hε, hε1, hgood⟩ := exists_good_ball f L hc
  have hY := analyticAt_yF f L hc b
  have hZ := analyticAt_zF f c (w := 0) (by simp)
  refine (AnalyticAt.frequently_eq_iff_eventually_eq (by fun_prop) (by
    have := hY.deriv; have := hZ.deriv; fun_prop)).1 ?_
  refine Filter.Eventually.frequently ?_
  have hball : Metric.ball (0 : ℂ) ε ∈ nhds (0 : ℂ) := Metric.ball_mem_nhds 0 hε
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with w hw hw0
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hw0' : w ≠ 0 := hw0
  obtain ⟨hV, hZL⟩ := hgood w hw
  have hzL := hZL hw0'
  -- `Ŷ = w²(℘∘Z − b)` near `w`
  have hopen : IsOpen {v : ℂ | v ≠ 0 ∧ ‖v‖ < ε} :=
    isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
  have hev : yF f L c b =ᶠ[nhds w] fun v => v ^ 2 * (L.weierstrassP (zF f c v) - b) := by
    filter_upwards [hopen.mem_nhds ⟨hw0', hw⟩] with v hv
    exact yF_eq f L hc b (hgood v hv.2).1 hv.1
  have hZw : HasDerivAt (zF f c) (deriv (zF f c) w) w :=
    (analyticAt_zF f c (by linarith : ‖w‖ < 1)).differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun v => v ^ 2 * (L.weierstrassP (zF f c v) - b))
      (2 * w * (L.weierstrassP (zF f c w) - b) +
        w ^ 2 * (L.derivWeierstrassP (zF f c w) * deriv (zF f c) w)) w := by
    have h1 : HasDerivAt (fun v : ℂ => v ^ 2) (2 * w) w := by
      simpa using hasDerivAt_pow 2 w
    have h2 := ((hasDerivAt_wp L hzL).comp w hZw).sub_const b
    exact h1.mul h2
  rw [hev.deriv_eq, hd.deriv, yF_eq f L hc b hV hw0']
  have hsq := L.derivWeierstrassP_sq _ hzL
  set P := L.weierstrassP (zF f c w)
  set P' := L.derivWeierstrassP (zF f c w)
  set Z' := deriv (zF f c) w
  have e1 : w * (2 * w * (P - b) + w ^ 2 * (P' * Z')) - 2 * (w ^ 2 * (P - b)) = w ^ 3 * P' * Z' := by
    ring
  rw [e1]
  linear_combination (w ^ 6 * Z' ^ 2) * hsq

theorem C_two : (PowerSeries.C (2 : ℂ) : ℂ⟦X⟧) = 2 := map_ofNat _ 2
theorem C_four : (PowerSeries.C (4 : ℂ) : ℂ⟦X⟧) = 4 := map_ofNat _ 4

/-- **The formal Weierstrass equation for the Taylor series of `Ŷ`.** -/
theorem tay_yF_ode {c : ℂ} (hc : c ≠ 0) (b : ℂ) :
    odePhi (d⁄dX (tay (zF f c)) ^ 2) b L.g₂ L.g₃ (tay (yF f L c b)) = 0 := by
  set Y := yF f L c b with hYdef
  set Z := zF f c with hZdef
  have hY : AnalyticAt ℂ Y 0 := analyticAt_yF f L hc b
  have hdY := hY.deriv
  have hZ : AnalyticAt ℂ Z 0 := analyticAt_zF f c (w := 0) (by simp)
  have hdZ := hZ.deriv
  have h := tay_congr (yF_ode f L hc b)
  -- left side
  have l1 := tay_pow (f := fun w => w * deriv Y w - 2 * Y w) (by fun_prop) 2
  have l2 := tay_sub (f := fun w => w * deriv Y w) (g := fun w => 2 * Y w) (by fun_prop)
    (by fun_prop)
  have l3 := tay_mul (f := fun w => w) (g := deriv Y) analyticAt_id hdY
  have l4 := tay_cmul 2 hY
  beta_reduce at l1 l2 l3 l4
  -- right side
  set U := fun w => Y w + b * w ^ 2 with hUdef
  have hU : AnalyticAt ℂ U 0 := by fun_prop
  have r1 := tay_mul (f := fun w => 4 * U w ^ 3 - L.g₂ * w ^ 4 * U w - L.g₃ * w ^ 6)
    (g := fun w => deriv Z w ^ 2) (by fun_prop) (by fun_prop)
  have r2 := tay_pow (f := deriv Z) hdZ 2
  have r3 := tay_sub (f := fun w => 4 * U w ^ 3 - L.g₂ * w ^ 4 * U w) (g := fun w => L.g₃ * w ^ 6)
    (by fun_prop) (by fun_prop)
  have r4 := tay_sub (f := fun w => 4 * U w ^ 3) (g := fun w => L.g₂ * w ^ 4 * U w)
    (by fun_prop) (by fun_prop)
  have r5 := tay_cmul 4 (f := fun w => U w ^ 3) (by fun_prop)
  have r6 := tay_pow hU 3
  have r7 := tay_mul (f := fun w => L.g₂ * w ^ 4) (g := U) (by fun_prop) hU
  have r8 := tay_cmul L.g₂ (f := fun w => w ^ 4) (by fun_prop)
  have r9 := tay_cmul L.g₃ (f := fun w => w ^ 6) (by fun_prop)
  have r10 := tay_add (f := Y) (g := fun w => b * w ^ 2) hY (by fun_prop)
  have r11 := tay_cmul b (f := fun w => w ^ 2) (by fun_prop)
  beta_reduce at r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  have hUt : tay U = tay Y + PowerSeries.C b * X ^ 2 := by
    rw [hUdef, r10, r11, tay_X_pow]
  rw [l1, l2, l3, l4, tay_id, tay_deriv hY, C_two] at h
  rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, tay_X_pow, tay_X_pow, tay_deriv hZ, hUt, C_four] at h
  unfold odePhi
  rw [h, sub_self]

/-- `tay Z = c·X·tay V`. -/
theorem tay_zF (c : ℂ) : tay (zF f c) = C c * X * tay (vFun f) := by
  have hV := analyticAt_vFun f
  have e : zF f c = fun w => c * w * vFun f w := rfl
  have h1 := tay_mul (f := fun w => c * w) (g := vFun f) (by fun_prop) hV
  have h2 := tay_cmul c (f := fun w => w) analyticAt_id
  beta_reduce at h1 h2
  rw [e, h1, h2, tay_id]

theorem map_tay_vFun (hV : ∀ n, ∃ q : ℚ, eCoeff f n = q) (σ : ℂ →+* ℂ) :
    PowerSeries.map σ (tay (vFun f)) = tay (vFun f) := by
  ext n
  rw [PowerSeries.coeff_map, coeff_tay_vFun]
  obtain ⟨q, hq⟩ := hV (n + 1)
  rw [hq, map_ratCast]

theorem map_tay_zF (hV : ∀ n, ∃ q : ℚ, eCoeff f n = q) (c : ℚ) (σ : ℂ →+* ℂ) :
    PowerSeries.map σ (tay (zF f c)) = tay (zF f c) := by
  rw [tay_zF, map_mul, map_mul, PowerSeries.map_C, PowerSeries.map_X, map_tay_vFun f hV σ,
    map_ratCast]

/-- **The Taylor series of `Ŷ` is fixed by `Aut(ℂ)`** (all data rational; uniqueness of the formal
solution). -/
theorem map_tay_yF (hV : ∀ n, ∃ q : ℚ, eCoeff f n = q) {c : ℚ} (hc : c ≠ 0) (b : ℚ) {g₂ g₃ : ℚ}
    (hg₂ : L.g₂ = g₂) (hg₃ : L.g₃ = g₃) (σ : ℂ →+* ℂ) :
    PowerSeries.map σ (tay (yF f L c b)) = tay (yF f L c b) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hode := tay_yF_ode f L hc' b
  rw [hg₂, hg₃] at hode
  set A := d⁄dX (tay (zF f c)) ^ 2 with hAdef
  have hAfix : PowerSeries.map σ A = A := by
    rw [hAdef, map_pow, map_derivative, map_tay_zF f hV c σ]
  have hS : odePhi A b g₂ g₃ (PowerSeries.map σ (tay (yF f L c b))) = 0 := by
    have := congrArg (PowerSeries.map σ) hode
    rw [map_odePhi, map_zero, hAfix, map_ratCast, map_ratCast, map_ratCast] at this
    exact this
  refine (odePhi_unique A b g₂ g₃ hode hS ?_ ?_ ?_).symm
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_tay, yF_zero]
    rw [show ((c : ℂ) ^ 2)⁻¹ = (((c ^ 2)⁻¹ : ℚ) : ℂ) by push_cast; rfl, map_ratCast]
  · rw [constantCoeff_tay, yF_zero]; simpa using hc'
  · rw [hAdef, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_derivative, tay_zF, constantCoeff_tay, yF_zero,
      show (C (c : ℂ) * X * tay (vFun f)) = C (c : ℂ) * (X * tay (vFun f)) by ring]
    simp only [zero_add, Nat.cast_zero, PowerSeries.coeff_C_mul, mul_one]
    rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_tay, vFun_zero]
    field_simp

/-- A rational Laurent expansion in `q = e^{2πiτ}` valid for `Im τ > T`. -/
def HasRatQExp (g : UpperHalfPlane → ℂ) : Prop :=
  ∃ (k : ℕ) (a : ℕ → ℚ) (T : ℝ), ∀ τ : UpperHalfPlane, T < τ.im →
    HasSum (fun n : ℕ => (a n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * τ) ^ n)
      (Complex.exp (2 * Real.pi * Complex.I * τ) ^ k * g τ)

/-- **A rational `q`-expansion from a Taylor series fixed by `Aut(ℂ)`.** -/
theorem hasRatQExp_of_tay (g : UpperHalfPlane → ℂ) (W : ℂ → ℂ) (hW : AnalyticAt ℂ W 0)
    (hfix : ∀ σ : ℂ ≃+* ℂ, PowerSeries.map (σ : ℂ →+* ℂ) (tay W) = tay W) (k : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hg : ∀ τ : UpperHalfPlane, ‖qC τ‖ < ε → qC τ ^ k * g τ = W (qC τ)) :
    HasRatQExp g := by
  have hrat : ∀ n, ∃ a : ℚ, (a : ℂ) = PowerSeries.coeff n (tay W) := fun n =>
    rat_of_fixed _ fun σ => by
      have := congrArg (PowerSeries.coeff n) (hfix σ)
      rwa [PowerSeries.coeff_map] at this
  choose a ha using hrat
  obtain ⟨r, hr, hAn⟩ := hW.exists_ball_analyticOnNhd
  set ρ := min ε r
  have hρ : 0 < ρ := lt_min hε hr
  refine ⟨k, a, |Real.log ρ| / (2 * Real.pi) + 1, fun τ hτ => ?_⟩
  have hq : ‖qC τ‖ < ρ := by
    rw [qC, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * τ).re = -(2 * Real.pi * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have hπ := Real.pi_pos
    have h1 : -(2 * Real.pi * τ.im) < Real.log ρ := by
      have hA : |Real.log ρ| / (2 * Real.pi) < τ.im := by linarith
      rw [div_lt_iff₀ (by positivity)] at hA
      linarith [neg_abs_le (Real.log ρ)]
    calc Real.exp (-(2 * Real.pi * τ.im)) < Real.exp (Real.log ρ) := Real.exp_lt_exp.2 h1
      _ = ρ := Real.exp_log hρ
  have hqε : ‖qC τ‖ < ε := lt_of_lt_of_le hq (min_le_left _ _)
  have hqr : qC τ ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hq (min_le_right _ _)
  have hs := Complex.hasSum_taylorSeries_on_ball (hAn.differentiableOn) hqr
  rw [show Complex.exp (2 * Real.pi * Complex.I * τ) = qC τ from rfl, hg τ hqε]
  convert hs using 1
  funext n
  rw [ha n, coeff_tay, sub_zero, smul_eq_mul, smul_eq_mul]
  ring

/-- The fixed-by-`Aut(ℂ)` property is inherited through a product with a fixed series. -/
theorem fixed_of_mul {T U R : ℂ⟦X⟧} (hU : U ≠ 0) (h : T * U = R) (σ : ℂ →+* ℂ)
    (hUf : PowerSeries.map σ U = U) (hRf : PowerSeries.map σ R = R) :
    PowerSeries.map σ T = T := by
  have := congrArg (PowerSeries.map σ) h
  rw [map_mul, hUf, hRf, ← h] at this
  exact mul_right_cancel₀ hU this

theorem hasDerivAt_zF_zero (c : ℂ) : HasDerivAt (zF f c) c 0 := by
  have hV := (analyticAt_vFun f).differentiableAt.hasDerivAt
  have h := ((hasDerivAt_id (0 : ℂ)).const_mul c).mul hV
  convert h using 1
  · funext w; simp [zF]
  · simp [vFun_zero]

theorem eCoeff_rat (E : WeierstrassCurve ℚ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) (n : ℕ) :
    ∃ q : ℚ, eCoeff f n = q := by
  unfold eCoeff
  split_ifs with hn
  · exact ⟨0, by simp⟩
  · exact ⟨((E.LFunction n : ℤ) : ℚ) / n, by rw [hcoeff n hn]; push_cast; ring⟩

/-- **(GLUE, analysis) Rational `q`-expansions of the coordinates of `φ`.** Near `∞`,
`c φ_f(τ) = c q + …` has rational coefficients (`aₙ(f) = aₙ(E) ∈ ℤ`, `c ∈ ℚ`), and the Laurent
expansion of `℘_L` at `0` has coefficients in `ℚ[g₂, g₃] = ℚ` (`g₂ = c₄/12`, `g₃ = c₆/216`), so
`x∘φ = c⁻²q⁻² + …`, `y∘φ`, `1/(x∘φ − t)` are Laurent series in `q` with rational coefficients. -/
def ParamQExpansion : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2)
    (L : PeriodPair) (c : ℚ), ParamSetting E f L c →
    HasRatQExp (xPar E L f c) ∧ HasRatQExp (yPar E L f c) ∧ ∀ t : ℚ, HasRatQExp (gPar E L f c t)

/-- **`ParamQExpansion`, proved.** -/
theorem paramQExpansion : ParamQExpansion := by
  intro E _ N _ f L c hs
  obtain ⟨-, hcoeff, hL, hc, -⟩ := hs
  have hV := eCoeff_rat f E hcoeff
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  -- rational constants
  set bq : ℚ := E.b₂ / 12
  have hb : (E⁄ℂ).b₂ / 12 = (bq : ℂ) := by
    simp [bq, WeierstrassCurve.baseChange, WeierstrassCurve.map_b₂]
  have hg₂ : L.g₂ = ((E.c₄ / 12 : ℚ) : ℂ) := by
    rw [hL.1]; simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄]
  have hg₃ : L.g₃ = ((E.c₆ / 216 : ℚ) : ℂ) := by
    rw [hL.2]; simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₆]
  have ha₁ : (E⁄ℂ).a₁ = ((E.a₁ : ℚ) : ℂ) := by simp [WeierstrassCurve.baseChange]
  have ha₃ : (E⁄ℂ).a₃ = ((E.a₃ : ℚ) : ℂ) := by simp [WeierstrassCurve.baseChange]
  set Y := yF f L c bq with hYdef
  set Z := zF f c with hZdef
  have hY : AnalyticAt ℂ Y 0 := analyticAt_yF f L hc' _
  have hdY := hY.deriv
  have hZ : AnalyticAt ℂ Z 0 := analyticAt_zF f c (w := 0) (by simp)
  have hdZ := hZ.deriv
  have hYfix : ∀ σ : ℂ →+* ℂ, PowerSeries.map σ (tay Y) = tay Y := fun σ =>
    map_tay_yF f L hV hc bq hg₂ hg₃ σ
  have hZfix : ∀ σ : ℂ →+* ℂ, PowerSeries.map σ (tay Z) = tay Z := fun σ => map_tay_zF f hV c σ
  obtain ⟨ε, hε, hε1, hgood⟩ := exists_good_ball f L hc'
  -- `zPar = Z(q)`
  have hz : ∀ τ : UpperHalfPlane, zPar f c τ = Z (qC τ) := by
    intro τ
    rw [zPar, eichler_eq, eSum_eq_mul_vFun f _ (norm_qC_lt_one τ.im_pos)]
    simp only [hZdef, zF]; ring
  have hx : ∀ τ : UpperHalfPlane, ‖qC τ‖ < ε → qC τ ^ 2 * xPar E L f c τ = Y (qC τ) := by
    intro τ hτ
    have hq0 : qC τ ≠ 0 := Complex.exp_ne_zero _
    rw [xPar, hz, hb, hYdef, yF_eq f L hc' _ (hgood _ hτ).1 hq0]
  have hY0 : Y 0 = ((c : ℂ) ^ 2)⁻¹ := yF_zero f L _ _
  refine ⟨hasRatQExp_of_tay _ Y hY (fun σ => hYfix σ) 2 hε hx, ?_, fun t => ?_⟩
  · -- `y∘φ`
    set W : ℂ → ℂ := fun w => ((w * deriv Y w - 2 * Y w) * (deriv Z w)⁻¹ -
      (E.a₁ : ℂ) * w * Y w - (E.a₃ : ℂ) * w ^ 3) / 2 with hWdef
    have hdZ0 : deriv Z 0 ≠ 0 := by rw [(hasDerivAt_zF_zero f c).deriv]; exact hc'
    have hW : AnalyticAt ℂ W 0 := by
      have := hdZ.inv hdZ0
      rw [hWdef]; fun_prop
    have hev : (fun w => W w * (2 * deriv Z w)) =ᶠ[nhds 0]
        fun w => (w * deriv Y w - 2 * Y w) - ((E.a₁ : ℂ) * w * Y w + (E.a₃ : ℂ) * w ^ 3) *
          deriv Z w := by
      filter_upwards [hdZ.continuousAt.eventually_ne hdZ0] with w hw
      rw [hWdef]; field_simp; ring
    have ht := tay_congr hev
    have l1 := tay_mul (f := W) (g := fun w => 2 * deriv Z w) hW (by fun_prop)
    have l2 := tay_cmul 2 hdZ
    have r1 := tay_sub (f := fun w => w * deriv Y w - 2 * Y w)
      (g := fun w => ((E.a₁ : ℂ) * w * Y w + (E.a₃ : ℂ) * w ^ 3) * deriv Z w)
      (by fun_prop) (by fun_prop)
    have r2 := tay_sub (f := fun w => w * deriv Y w) (g := fun w => 2 * Y w) (by fun_prop)
      (by fun_prop)
    have r3 := tay_mul (f := fun w => w) (g := deriv Y) analyticAt_id hdY
    have r4 := tay_cmul 2 hY
    have r5 := tay_mul (f := fun w => (E.a₁ : ℂ) * w * Y w + (E.a₃ : ℂ) * w ^ 3) (g := deriv Z)
      (by fun_prop) hdZ
    have r6 := tay_add (f := fun w => (E.a₁ : ℂ) * w * Y w) (g := fun w => (E.a₃ : ℂ) * w ^ 3)
      (by fun_prop) (by fun_prop)
    have r7 := tay_mul (f := fun w => (E.a₁ : ℂ) * w) (g := Y) (by fun_prop) hY
    have r8 := tay_cmul (E.a₁ : ℂ) (f := fun w => w) analyticAt_id
    have r9 := tay_cmul (E.a₃ : ℂ) (f := fun w => w ^ 3) (by fun_prop)
    beta_reduce at l1 l2 r1 r2 r3 r4 r5 r6 r7 r8 r9
    rw [l1, l2, r1, r2, r3, r4, r5, r6, r7, r8, r9, tay_id, tay_X_pow, tay_deriv hY,
      tay_deriv hZ] at ht
    obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 (hdZ.continuousAt.eventually_ne hdZ0)
    refine hasRatQExp_of_tay _ W hW (fun σ => fixed_of_mul ?_ ht σ ?_ ?_) 3 (lt_min hε hδ) ?_
    · intro h0
      have := congrArg PowerSeries.constantCoeff h0
      have h1 : PowerSeries.constantCoeff (d⁄dX (tay Z)) = deriv Z 0 := by
        rw [← tay_deriv hZ, constantCoeff_tay]
      rw [map_mul, PowerSeries.constantCoeff_C, h1, map_zero] at this
      exact hdZ0 ((mul_eq_zero.1 this).resolve_left two_ne_zero)
    · rw [map_mul, PowerSeries.map_C, map_derivative, hZfix, map_ofNat]
    · simp only [map_sub, map_mul, map_add, map_pow, PowerSeries.map_X, PowerSeries.map_C,
        map_derivative, hYfix, hZfix, map_ofNat, map_ratCast]
    · intro τ hτ
      have hτε : ‖qC τ‖ < ε := lt_of_lt_of_le hτ (min_le_left _ _)
      have hq0 : qC τ ≠ 0 := Complex.exp_ne_zero _
      have hdZq : deriv Z (qC τ) ≠ 0 :=
        hδb (by rw [dist_zero_right]; exact lt_of_lt_of_le hτ (min_le_right _ _))
      have hderiv := yF_deriv_eq f L hc' bq hε1 hgood hτε hq0
      have hxq := hx τ hτε
      rw [yPar, hWdef]
      simp only
      rw [hderiv, ha₁, ha₃, hz τ, ← hxq]
      field_simp
      ring
  · -- `1/(x∘φ − t)`
    set W : ℂ → ℂ := fun w => w ^ 2 * (Y w - t * w ^ 2)⁻¹ with hWdef
    have hU0 : Y 0 - t * 0 ^ 2 ≠ 0 := by rw [hY0]; simpa using hc'
    have hUa : AnalyticAt ℂ (fun w => Y w - t * w ^ 2) 0 := by fun_prop
    have hW : AnalyticAt ℂ W 0 := by
      have := hUa.inv hU0
      rw [hWdef]; fun_prop
    have hev : (fun w => W w * (Y w - t * w ^ 2)) =ᶠ[nhds 0] fun w => w ^ 2 := by
      filter_upwards [hUa.continuousAt.eventually_ne hU0] with w hw
      rw [hWdef]; simp only; rw [mul_assoc, inv_mul_cancel₀ hw, mul_one]
    have ht := tay_congr hev
    have l1 := tay_mul (f := W) (g := fun w => Y w - t * w ^ 2) hW hUa
    have l2 := tay_sub (f := Y) (g := fun w => (t : ℂ) * w ^ 2) hY (by fun_prop)
    have l3 := tay_cmul (t : ℂ) (f := fun w => w ^ 2) (by fun_prop)
    beta_reduce at l1 l2 l3
    rw [l1, l2, l3, tay_X_pow] at ht
    refine hasRatQExp_of_tay _ W hW (fun σ => fixed_of_mul ?_ ht σ ?_ ?_) 0 hε ?_
    · intro h0
      have := congrArg PowerSeries.constantCoeff h0
      rw [map_sub, map_mul, map_pow, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
        constantCoeff_tay, map_zero] at this
      exact hU0 (by simpa using this)
    · rw [map_sub, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hYfix, map_ratCast]
    · rw [map_pow, PowerSeries.map_X]
    · intro τ hτ
      have hq0 : qC τ ≠ 0 := Complex.exp_ne_zero _
      have hxq := hx τ hτ
      have hzL : zPar f c τ ∉ L.lattice := by rw [hz τ]; exact (hgood _ hτ).2 hq0
      rw [pow_zero, one_mul, gPar, if_neg hzL, hWdef]
      simp only
      rw [← hxq]
      have hq2 : qC τ ^ 2 ≠ 0 := pow_ne_zero 2 hq0
      rw [show qC τ ^ 2 * xPar E L f c τ - t * qC τ ^ 2 = qC τ ^ 2 * (xPar E L f c τ - t) by ring,
        mul_inv, ← mul_assoc, mul_inv_cancel₀ hq2, one_mul]

end QExp

end ZInQ.GZHeegner

#print axioms ZInQ.GZHeegner.paramQExpansion
