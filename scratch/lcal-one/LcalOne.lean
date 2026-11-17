import ZInQKernel.Contrib.TYZChain.Lcal
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.JacobiLambdaDeriv
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilJacobi
import ZInQKernel.Contrib.GZTheta.EtaTheta
import ZInQKernel.Contrib.OneProof.TYZThm11Genus

/-!
# lcal-one: `TYZLcalOne` proved (`L(y² = x³ − x, 1) = ¼ ∫₁^∞ dx/√(x³ − x)`)

Task lcal-one (2026-11-16). Report: `docs/research/lcal-one.md`; development file and log: `scratch/lcal-one/`.

`ZInQ.Contrib.TYZDecomp.TYZLcalOne` (`lcalSq 1 = 1`, TYZ's `𝓛(1) = 1`, asserted at L1082 of arXiv:1411.4728v1) is
the exact evaluation `L(C₁, 1) = Ω/4`, `Ω = ∫₁^∞ dx/√(x³ − x)` (the real period of `C₁ : y² = x³ − x` is `2Ω`, so
`L(C₁, 1)/Ω_{C₁} = 1/8`). It is proved here from theorems already in the tree, with no new hypothesis:

* **Part A** (`lValOne_one_eq_integral`): `L(C₁, 1) = 2π ∫₀^∞ f(it) dt`, `f = η(4τ)²η(8τ)²`. The tree's
  continuation (`TYZLcal.lValOne_one_eq`) writes `L(C₁, 1)` through the Mellin transforms at `s = 1` of the shifted
  lattice theta kernels `Θ_{j/4}`; the block decomposition of `ℤ[i]` modulo `4` and the grouping by the norm turn
  `Σ_j cU(j) Θ_{j/4}(x)` into `¼ Σ_n a_n e^{−πnx/16}`, which is `¼ f(ix/32)` by gz-theta's `etaThetaIdentity`.
* **Part B** (`integral_Fr`): `∫₀^∞ f(it) dt = Ω/(8π)`. On the imaginary axis x0-32's eta quotients `x, y`
  (`y² = x³ + 4x`, tyz-cm) are real, `y < 0 < f`, and `x' = −4π f y` (`X0.EtaModelDifferential`, proved by
  gz-weil from Jacobi's derivative formula). By the theta `S`-law `x(it) → 2` as `t → 0⁺` (the cusp `0` goes to
  `(2, −4)`) and `x(it) → ∞` as `t → ∞`. The substitution `u = x/4 + 1/x` (the `2`-isogeny
  `y² = x³ + 4x → Y² = X³ − 16X`, `X = x + 4/x = 4u`) maps `(0, ∞)` onto `(1, ∞)` with
  `u'/√(u³ − u) = 8π f(it)`, and the fundamental theorem of calculus on `(0, ∞)` for `K(u(t))`,
  `K(u) = ¼ ∫_u^∞ dv/√(v³ − v)`, gives the value.

Main results: `tyzLcalOne_proof : TYZLcalOne`, `lValOne_one : lValOne 1 = Ω/4`, and
`tyzThm11Integral_of_thm21C_only : TYZThm21PairsC → TYZThm11Integral` (tyz-genus's
`tyzThm11Integral_of_thm21C` with `TYZLcalOne` discharged). No `sorry`, no `axiom`, no code run at build time.
-/

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace ZInQ.Contrib.LcalOne

open ZInQ.Contrib.TYZGenus

/-! ## The eta model on the imaginary axis -/

/-- The point `i t` of `ℍ`. -/
def iT (t : ℝ) (ht : 0 < t) : UpperHalfPlane := ⟨I * t, by simpa using ht⟩

theorem coe_iT (t : ℝ) (ht : 0 < t) : ((iT t ht : UpperHalfPlane) : ℂ) = I * t := rfl

theorem neg_conj_I_mul (t : ℝ) : -(starRingEnd ℂ) (I * (t : ℂ)) = I * t := by
  simp [map_mul, Complex.conj_I, Complex.conj_ofReal]

theorem re_eq_of_neg_conj {f : ℂ → ℂ} (hf : ∀ z, f (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (t : ℝ) : ((f (I * t)).re : ℂ) = f (I * t) := by
  rw [← Complex.conj_eq_iff_re, ← hf, neg_conj_I_mul]

/-- `x(it)`, `y(it)`, `f(it)`, `η(d · it)` as real numbers. -/
def Xr (t : ℝ) : ℝ := (X0.xC (I * t)).re
def Yr (t : ℝ) : ℝ := (X0.yC (I * t)).re
def Fr (t : ℝ) : ℝ := (X0.fC (I * t)).re
def Er (d : ℕ) (t : ℝ) : ℝ := (X0.etaD d (I * t)).re

theorem Xr_eq (t : ℝ) : (Xr t : ℂ) = X0.xC (I * t) := re_eq_of_neg_conj X0.xC_neg_conj t
theorem Yr_eq (t : ℝ) : (Yr t : ℂ) = X0.yC (I * t) := re_eq_of_neg_conj X0.yC_neg_conj t
theorem Fr_eq (t : ℝ) : (Fr t : ℂ) = X0.fC (I * t) := re_eq_of_neg_conj X0.fC_neg_conj t
theorem Er_eq (d : ℕ) (t : ℝ) : (Er d t : ℂ) = X0.etaD d (I * t) :=
  re_eq_of_neg_conj (X0.etaD_neg_conj d) t

theorem Er_ne_zero {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) : Er d t ≠ 0 := by
  intro h
  have := X0.etaD_ne_zero hd (iT t ht)
  rw [coe_iT, ← Er_eq, h, ofReal_zero] at this
  exact this rfl

theorem Fr_pos {t : ℝ} (ht : 0 < t) : 0 < Fr t := by
  have e : (Fr t : ℂ) = ((Er 4 t ^ 2 * Er 8 t ^ 2 : ℝ) : ℂ) := by
    rw [Fr_eq, X0.fC]; push_cast; rw [Er_eq, Er_eq]
  have := ofReal_injective e
  rw [this]
  have h4 := Er_ne_zero (by norm_num : 0 < 4) ht
  have h8 := Er_ne_zero (by norm_num : 0 < 8) ht
  positivity

theorem Yr_neg {t : ℝ} (ht : 0 < t) : Yr t < 0 := by
  have e : (Yr t : ℂ) = ((-(Er 8 t ^ 4 * Er 16 t ^ 2 / (Er 4 t ^ 2 * Er 32 t ^ 4)) : ℝ) : ℂ) := by
    rw [Yr_eq, X0.yC]; push_cast; rw [Er_eq, Er_eq, Er_eq, Er_eq]
  have := ofReal_injective e
  rw [this]
  have h4 := Er_ne_zero (by norm_num : 0 < 4) ht
  have h8 := Er_ne_zero (by norm_num : 0 < 8) ht
  have h16 := Er_ne_zero (by norm_num : 0 < 16) ht
  have h32 := Er_ne_zero (by norm_num : 0 < 32) ht
  have : 0 < Er 8 t ^ 4 * Er 16 t ^ 2 / (Er 4 t ^ 2 * Er 32 t ^ 4) := by positivity
  linarith

theorem Yr_sq {t : ℝ} (ht : 0 < t) : Yr t ^ 2 = Xr t ^ 3 + 4 * Xr t := by
  have h := Shimura.etaModelEquation (iT t ht)
  rw [coe_iT, ← Xr_eq, ← Yr_eq] at h
  exact_mod_cast h

theorem Xr_pos {t : ℝ} (ht : 0 < t) : 0 < Xr t := by
  have h1 := Yr_sq ht
  have h2 := Yr_neg ht
  have h3 : 0 < Yr t ^ 2 := by nlinarith
  nlinarith [sq_nonneg (Xr t)]

/-- **`x(it)' = −4π f(it) y(it)`** (x0-32's differential, proved by gz-weil). -/
theorem hasDerivAt_Xr {t : ℝ} (ht : 0 < t) :
    HasDerivAt Xr (-4 * π * Fr t * Yr t) t := by
  have h := ZInQ.GZWeil.etaModelDifferential (iT t ht)
  rw [coe_iT] at h
  have h2 : HasDerivAt (fun z : ℂ => X0.xC (I * z)) (4 * π * I * X0.fC (I * t) * X0.yC (I * t) * I)
      (t : ℂ) := by
    have hl : HasDerivAt (fun z : ℂ => I * z) I (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).const_mul I
    exact h.comp (t : ℂ) hl
  have h3 := h2.real_of_complex
  have key : (4 * π * I * X0.fC (I * t) * X0.yC (I * t) * I).re = -4 * π * Fr t * Yr t := by
    rw [← Fr_eq, ← Yr_eq]
    have : (4 * π * I * (Fr t : ℂ) * (Yr t : ℂ) * I) = ((-4 * π * Fr t * Yr t : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [this, ofReal_re]
  exact h3.congr_deriv key

theorem Xr_deriv_pos {t : ℝ} (ht : 0 < t) : 0 < -4 * π * Fr t * Yr t := by
  have h1 := Fr_pos ht
  have h2 := Yr_neg ht
  have hp := Real.pi_pos
  have : 0 < Fr t * (-Yr t) := mul_pos h1 (neg_pos.mpr h2)
  nlinarith

theorem continuousOn_Xr : ContinuousOn Xr (Ioi 0) := fun _ ht =>
  (hasDerivAt_Xr ht).continuousAt.continuousWithinAt

theorem strictMonoOn_Xr : StrictMonoOn Xr (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) continuousOn_Xr fun t ht => ?_
  rw [interior_Ioi] at ht
  rw [(hasDerivAt_Xr ht).deriv]
  exact Xr_deriv_pos ht

/-! ## Limits of `x(it)` at `0⁺` and at `∞` -/

open ZInQ.GZWeil (thetaTwo thetaThree thetaFour)

theorem xC_eq_ratio (τ : UpperHalfPlane) :
    X0.xC τ = 2 * thetaThree (16 * τ) / thetaTwo (16 * τ) := by
  rw [Shimura.xC_theta, ZInQ.GZWeil.thetaTwo_sixteen]
  rfl

theorem tendsto_exp_neg_pi_mul : Tendsto (fun y : ℝ => 3 * Real.exp (-π * y)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => π * y) atTop atTop := tendsto_id.const_mul_atTop Real.pi_pos
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have h3 := h2.const_mul 3
  rw [mul_zero] at h3
  refine h3.congr fun y => ?_
  simp [Function.comp, neg_mul]

theorem im_I_mul (y : ℝ) : (I * (y : ℂ)).im = y := by simp

theorem tendsto_thetaThree_atTop : Tendsto (fun y : ℝ => thetaThree (I * y)) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ tendsto_exp_neg_pi_mul
  filter_upwards [eventually_ge_atTop 1] with y hy
  have := ZInQ.JacobiLambda.norm_thetaThree_sub_one_le (s := I * y) (by rw [im_I_mul]; exact hy)
  rwa [im_I_mul] at this

theorem tendsto_thetaFour_atTop : Tendsto (fun y : ℝ => thetaFour (I * y)) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ tendsto_exp_neg_pi_mul
  filter_upwards [eventually_ge_atTop 1] with y hy
  have := ZInQ.JacobiLambda.norm_thetaFour_sub_one_le (s := I * y) (by rw [im_I_mul]; exact hy)
  rwa [im_I_mul] at this

theorem tendsto_thT_atTop :
    Tendsto (fun y : ℝ => ZInQ.JacobiLambda.thT (I * y)) atTop (𝓝 2) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ tendsto_exp_neg_pi_mul
  filter_upwards [eventually_ge_atTop 1] with y hy
  have := ZInQ.JacobiLambda.norm_thT_sub_two_le (s := I * y) (by rw [im_I_mul]; exact hy)
  rwa [im_I_mul] at this

theorem tendsto_inv_sixteen : Tendsto (fun t : ℝ => 1 / (16 * t)) (𝓝[>] 0) atTop := by
  have h : Tendsto (fun t : ℝ => 16 * t) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => 16 * t) (𝓝 0) (𝓝 (16 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos (by norm_num : (0:ℝ) < 16) ht
  exact h.inv_tendsto_nhdsGT_zero.congr fun t => by simp [one_div]

/-- `x(it)² = 4 θ₃(τ)²/θ₄(τ)²` with `τ = i/(16t)` (the `S`-law). -/
theorem Xr_sq_eq {t : ℝ} (ht : 0 < t) :
    ((Xr t ^ 2 : ℝ) : ℂ) = 4 * thetaThree (I * ((1 / (16 * t) : ℝ) : ℂ)) ^ 2 /
      thetaFour (I * ((1 / (16 * t) : ℝ) : ℂ)) ^ 2 := by
  set τ : ℂ := I * ((1 / (16 * t) : ℝ) : ℂ) with hτ
  have hτ0 : τ ≠ 0 := by
    rw [hτ]; refine mul_ne_zero I_ne_zero ?_
    exact_mod_cast (by positivity : (1 / (16 * t) : ℝ) ≠ 0)
  have hS : (16 : ℂ) * (I * t) = -1 / τ := by
    rw [eq_div_iff hτ0, hτ]
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have e : (16 : ℂ) * (I * t) * (I * ((1 / (16 * t) : ℝ) : ℂ)) = I ^ 2 := by
      push_cast; field_simp
    rw [e, I_sq]
  have h := xC_eq_ratio (iT t ht)
  rw [coe_iT, ← Xr_eq, hS] at h
  have h3 := ZInQ.GZWeil.thetaThree_S_sq hτ0
  have h2 := ZInQ.GZWeil.thetaTwo_S_sq hτ0
  have hτi : 0 < τ.im := by rw [hτ, im_I_mul]; positivity
  have h4 := ZInQ.GZWeil.thetaFour_ne_zero hτi
  have hT2 : thetaTwo (-1 / τ) ≠ 0 :=
    ZInQ.GZWeil.thetaTwo_ne_zero (ZInQ.GZWeil.im_neg_inv_pos hτi)
  push_cast
  rw [h, div_pow, mul_pow, h3, h2]
  field_simp
  ring

theorem tendsto_Xr_sq : Tendsto (fun t => Xr t ^ 2) (𝓝[>] 0) (𝓝 4) := by
  have h3 := tendsto_thetaThree_atTop.comp tendsto_inv_sixteen
  have h4 := tendsto_thetaFour_atTop.comp tendsto_inv_sixteen
  have hG : Tendsto (fun t : ℝ => 4 * thetaThree (I * ((1 / (16 * t) : ℝ) : ℂ)) ^ 2 /
      thetaFour (I * ((1 / (16 * t) : ℝ) : ℂ)) ^ 2) (𝓝[>] 0) (𝓝 4) := by
    have := ((h3.pow 2).const_mul 4).div (h4.pow 2) (by norm_num)
    convert this using 2
    all_goals norm_num
  have hC : Tendsto (fun t => ((Xr t ^ 2 : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 4) := by
    refine hG.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (Xr_sq_eq ht).symm
  have hR := (Complex.continuous_re.tendsto _).comp hC
  exact hR.congr fun t => Complex.ofReal_re _

/-- **`x(it) → 2` as `t → 0⁺`** (the cusp `0` goes to the point `(2, −4)`). -/
theorem tendsto_Xr_zero : Tendsto Xr (𝓝[>] 0) (𝓝 2) := by
  have h := (Real.continuous_sqrt.tendsto _).comp tendsto_Xr_sq
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact Real.sqrt_sq (Xr_pos ht).le

/-- `1/x(it) = e^{−4πt} T(16it) / (2 θ₃(16it))`. -/
theorem Xr_inv_eq {t : ℝ} (ht : 0 < t) :
    (((Xr t)⁻¹ : ℝ) : ℂ) = ((Real.exp (-(4 * π * t)) : ℝ) : ℂ) *
      ZInQ.JacobiLambda.thT (I * ((16 * t : ℝ) : ℂ)) / (2 * thetaThree (I * ((16 * t : ℝ) : ℂ))) := by
  have h := xC_eq_ratio (iT t ht)
  rw [coe_iT, ← Xr_eq] at h
  have e16 : (16 : ℂ) * (I * t) = I * ((16 * t : ℝ) : ℂ) := by push_cast; ring
  rw [e16] at h
  have hi : 0 < (I * ((16 * t : ℝ) : ℂ)).im := by rw [im_I_mul]; positivity
  have h3 := ZInQ.GZWeil.thetaThree_ne_zero hi
  have h2 := ZInQ.GZWeil.thetaTwo_ne_zero hi
  have he : cexp (π * I * (I * ((16 * t : ℝ) : ℂ)) / 4) = ((Real.exp (-(4 * π * t)) : ℝ) : ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  rw [ZInQ.JacobiLambda.thetaTwo_eq, he] at h2
  rw [ofReal_inv, h, ZInQ.JacobiLambda.thetaTwo_eq, he]
  field_simp

/-- **`x(it) → ∞` as `t → ∞`** (the cusp `∞` goes to `O`). -/
theorem tendsto_Xr_atTop : Tendsto Xr atTop atTop := by
  have h16 : Tendsto (fun t : ℝ => 16 * t) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
  have hT := tendsto_thT_atTop.comp h16
  have h3 := tendsto_thetaThree_atTop.comp h16
  have hE : Tendsto (fun t : ℝ => ((Real.exp (-(4 * π * t)) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 4 * π * t) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity)
    have := (Complex.continuous_ofReal.tendsto 0).comp (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1)
    rw [ofReal_zero] at this
    exact this
  have hC : Tendsto (fun t : ℝ => ((Real.exp (-(4 * π * t)) : ℝ) : ℂ) *
      ZInQ.JacobiLambda.thT (I * ((16 * t : ℝ) : ℂ)) / (2 * thetaThree (I * ((16 * t : ℝ) : ℂ))))
      atTop (𝓝 0) := by
    have := (hE.mul hT).div (h3.const_mul 2) (by norm_num)
    convert this using 2
    all_goals norm_num
  have hC' : Tendsto (fun t => (((Xr t)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    refine hC.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact (Xr_inv_eq ht).symm
  have hR : Tendsto (fun t => (Xr t)⁻¹) atTop (𝓝 0) := by
    have := (Complex.continuous_re.tendsto _).comp hC'
    exact this.congr fun t => Complex.ofReal_re _
  have hR' : Tendsto (fun t => (Xr t)⁻¹) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hR, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact inv_pos.mpr (Xr_pos ht)
  exact hR'.inv_tendsto_nhdsGT_zero.congr fun t => by simp

/-- **`x(it) > 2`** for `t > 0` (strictly increasing, limit `2` at `0⁺`). -/
theorem two_lt_Xr {t : ℝ} (ht : 0 < t) : 2 < Xr t := by
  by_contra hle'
  have hle := not_lt.mp hle'
  have ht1 : 0 < t / 2 := by positivity
  have hlt : Xr (t / 2) < Xr t := strictMonoOn_Xr ht1 ht (by linarith)
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), Xr s ≤ Xr (t / 2) := by
    filter_upwards [Ioo_mem_nhdsGT ht1] with s hs
    exact (strictMonoOn_Xr hs.1 ht1 hs.2).le
  have := le_of_tendsto tendsto_Xr_zero hev
  linarith

/-! ## The substitution `u = x/4 + 1/x` and the fundamental theorem of calculus -/

open ZInQ.Contrib.TYZDecomp (omegaInt)
open ZInQ.Contrib.TYZDecomp.OmegaInt (f f_measurable integrableOn_f)

/-- `u(t) = x(it)/4 + 1/x(it)`: the `2`-isogeny `y² = x³ + 4x → Y² = X³ − 16X`, `X = x + 4/x`,
followed by `X = 4u` (to `y² = u³ − u`). -/
def U (t : ℝ) : ℝ := Xr t / 4 + (Xr t)⁻¹

theorem one_lt_U {t : ℝ} (ht : 0 < t) : 1 < U t := by
  have hX := two_lt_Xr ht
  have hX0 := Xr_pos ht
  have e : U t - 1 = (Xr t - 2) ^ 2 / (4 * Xr t) := by
    unfold U; field_simp; ring
  have : 0 < (Xr t - 2) ^ 2 / (4 * Xr t) := div_pos (pow_pos (sub_pos.mpr hX) 2) (by positivity)
  linarith

theorem hasDerivAt_U {t : ℝ} (ht : 0 < t) :
    HasDerivAt U ((-4 * π * Fr t * Yr t) / 4 + -(-4 * π * Fr t * Yr t) / Xr t ^ 2) t := by
  have hX := hasDerivAt_Xr ht
  exact (hX.div_const 4).add (hX.inv (Xr_pos ht).ne')

/-- `√(u³ − u) = (x² − 4)/(8x²) · (−y)` on the imaginary axis. -/
theorem sqrt_U {t : ℝ} (ht : 0 < t) :
    Real.sqrt (U t ^ 3 - U t) = (Xr t ^ 2 - 4) / (8 * Xr t ^ 2) * (-Yr t) := by
  have hX := two_lt_Xr ht
  have hX0 := Xr_pos ht
  have hY := Yr_neg ht
  have hnn : 0 ≤ (Xr t ^ 2 - 4) / (8 * Xr t ^ 2) * (-Yr t) := by
    have : 0 ≤ Xr t ^ 2 - 4 := by nlinarith
    have : 0 ≤ -Yr t := by linarith
    positivity
  rw [← Real.sqrt_sq hnn]
  congr 1
  rw [mul_pow, neg_sq, Yr_sq ht]
  unfold U
  field_simp
  ring

/-- `∫₁^u dv/√(v³ − v)`. -/
def P (u : ℝ) : ℝ := ∫ v in (1 : ℝ)..u, f v

/-- `K(u) = ¼ ∫_u^∞ dv/√(v³ − v)`, written as `(Ω − P(u))/4`. -/
def K (u : ℝ) : ℝ := (omegaInt - P u) / 4

theorem K_one : K 1 = omegaInt / 4 := by simp [K, P]

theorem intervalIntegrable_f {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff]
  refine integrableOn_f.mono_set ?_
  intro x hx
  rw [Set.uIoc] at hx
  exact lt_of_le_of_lt (le_min ha hb) hx.1

theorem continuousAt_f {u : ℝ} (hu : 1 < u) : ContinuousAt f u := by
  have hpos : 0 < u ^ 3 - u := by
    have : 0 < u * (u - 1) * (u + 1) := mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    nlinarith
  unfold f
  refine continuousAt_const.div ?_ (Real.sqrt_pos.mpr hpos).ne'
  exact (Real.continuous_sqrt.comp (by fun_prop : Continuous fun x : ℝ => x ^ 3 - x)).continuousAt

theorem hasDerivAt_K {u : ℝ} (hu : 1 < u) : HasDerivAt K (-f u / 4) u := by
  have hP : HasDerivAt P (f u) u :=
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_f le_rfl hu.le)
      (f_measurable.stronglyMeasurable.stronglyMeasurableAtFilter) (continuousAt_f hu)
  exact (((hasDerivAt_const u omegaInt).sub hP).div_const 4).congr_deriv (by ring)

theorem continuousWithinAt_K : ContinuousWithinAt K (Ici 1) 1 := by
  have hP : ContinuousOn P (Set.uIcc 1 2) :=
    intervalIntegral.continuousOn_primitive_interval' (intervalIntegrable_f le_rfl (by norm_num))
      Set.left_mem_uIcc
  rw [Set.uIcc_of_le (by norm_num)] at hP
  have hP' : ContinuousWithinAt P (Ici 1) 1 :=
    (hP 1 ⟨le_rfl, by norm_num⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE (by norm_num))
  exact (continuousWithinAt_const.sub hP').div_const 4

theorem tendsto_K_atTop : Tendsto K atTop (𝓝 0) := by
  have hP : Tendsto P atTop (𝓝 omegaInt) :=
    intervalIntegral_tendsto_integral_Ioi 1 integrableOn_f tendsto_id
  have := (tendsto_const_nhds (x := omegaInt)).sub hP |>.div_const 4
  rw [sub_self, zero_div] at this
  exact this

/-- `ũ`: `u` on `(0, ∞)`, `1` elsewhere. -/
def Ut (t : ℝ) : ℝ := if 0 < t then U t else 1

/-- The primitive `G(t) = K(u(t))`, `G(0) = K(1) = Ω/4`. -/
def G (t : ℝ) : ℝ := K (Ut t)

theorem tendsto_U_zero : Tendsto U (𝓝[>] 0) (𝓝 1) := by
  have h := (tendsto_Xr_zero.div_const 4).add (tendsto_Xr_zero.inv₀ (by norm_num))
  have e : (2 : ℝ) / 4 + 2⁻¹ = 1 := by norm_num
  rw [e] at h
  exact h

theorem continuousWithinAt_G : ContinuousWithinAt G (Ici 0) 0 := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  have hU : Tendsto Ut (𝓝[>] 0) (𝓝[Ici 1] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_U_zero.congr' ?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp [Ut, show (0 : ℝ) < t from ht]
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Ut, show (0 : ℝ) < t from ht, ite_true]
      exact (one_lt_U ht).le
  have := continuousWithinAt_K.tendsto.comp hU
  have hG0 : G 0 = K 1 := by simp [G, Ut]
  rw [ContinuousWithinAt, hG0]
  exact this

theorem hasDerivAt_G {t : ℝ} (ht : 0 < t) : HasDerivAt G (-2 * π * Fr t) t := by
  have h := (hasDerivAt_K (one_lt_U ht)).comp t (hasDerivAt_U ht)
  have heq : G =ᶠ[𝓝 t] K ∘ U := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp [G, Ut, show (0 : ℝ) < s from hs]
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  have hX := two_lt_Xr ht
  have hX0 := Xr_pos ht
  have hY := Yr_neg ht
  have h4 : Xr t ^ 2 - 4 ≠ 0 := by nlinarith
  have hY0 : Yr t ≠ 0 := hY.ne
  unfold f
  rw [sqrt_U ht]
  field_simp
  ring

theorem tendsto_U_atTop : Tendsto U atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_Xr_atTop.atTop_div_const (by norm_num : (0:ℝ) < 4))
  filter_upwards [eventually_gt_atTop 0] with t ht
  have := Xr_pos ht
  unfold U
  have : 0 ≤ (Xr t)⁻¹ := by positivity
  linarith

theorem tendsto_G_atTop : Tendsto G atTop (𝓝 0) := by
  refine (tendsto_K_atTop.comp tendsto_U_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [G, Ut, ht]

/-- **`∫₀^∞ f(it) dt = Ω/(8π)`.** -/
theorem integral_Fr : ∫ t in Ioi (0 : ℝ), Fr t = omegaInt / (8 * π) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonpos continuousWithinAt_G
    (fun t ht => hasDerivAt_G ht) (fun t ht => by
      have := Fr_pos (show (0 : ℝ) < t from ht)
      have := Real.pi_pos
      nlinarith) tendsto_G_atTop
  have hG0 : G 0 = omegaInt / 4 := by simp [G, Ut, K_one]
  rw [hG0, MeasureTheory.integral_const_mul] at h
  have hp := Real.pi_pos
  field_simp
  linarith

/-! ## Part A: `L(C₁, 1) = 2π ∫₀^∞ f(it) dt` -/

open ZInQ.Contrib.HeckeFE

theorem norm_unitOf_le' (t : ZMod 4 × ZMod 4) : ‖unitOf t‖ ≤ 1 := by
  unfold unitOf
  split_ifs <;> simp

/-- The lattice theta series of `ψ₁`: `Σ_{α ∈ ℤ[i]} unitOf(α) α e^{−π N(α) x/16}`. -/
def latT (x : ℝ) (p : ℤ × ℤ) : ℂ :=
  unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4)) * gz 0 0 p * Real.exp (-π * gq 0 0 p * (x / 16))

theorem summable_latT {x : ℝ} (hx : 0 < x) : Summable (latT x) := by
  have h0 := (hasSum_gaussTheta 0 0 (t := x / 16) (by positivity)).summable
  have hn : Summable fun p : ℤ × ℤ => ‖gz 0 0 p * Real.exp (-π * gq 0 0 p * (x / 16))‖ :=
    summable_norm_iff.mpr h0
  refine Summable.of_norm_bounded hn fun p => ?_
  rw [latT, mul_assoc, norm_mul]
  calc ‖unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4))‖ *
        ‖gz 0 0 p * (Real.exp (-π * gq 0 0 p * (x / 16)) : ℂ)‖
      ≤ 1 * ‖gz 0 0 p * (Real.exp (-π * gq 0 0 p * (x / 16)) : ℂ)‖ :=
        mul_le_mul_of_nonneg_right (norm_unitOf_le' _) (norm_nonneg _)
    _ = _ := one_mul _

/-- **Block decomposition**: the lattice series is `Σ_j unitOf(j) · 4 · Θ_{j/4}(x)`. -/
theorem tsum_latT_block {x : ℝ} (hx : 0 < x) :
    ∑' p, latT x p = ∑ j : Fin 4 × Fin 4, 4 * unitOf (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4)) *
      gaussTheta (((j.1 : ℝ) / 4 : ℝ) : UnitAddCircle) (((j.2 : ℝ) / 4 : ℝ) : UnitAddCircle) x := by
  have hsum := summable_latT hx
  have h2 := (blockEquiv 4).summable_iff.mpr hsum
  rw [← (blockEquiv 4).tsum_eq]
  refine (h2.tsum_prod).trans ?_
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← (hasSum_gaussTheta ((j.1 : ℝ) / 4) ((j.2 : ℝ) / 4) hx).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  simp only [Function.comp_apply, latT]
  rw [gz_block, gq_block]
  have hc : unitOf ((((blockEquiv 4 (j, q)).1 : ℤ) : ZMod 4), (((blockEquiv 4 (j, q)).2 : ℤ) : ZMod 4)) =
      unitOf (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4)) := by
    have h4 : (4 : ZMod 4) = 0 := rfl
    simp [blockEquiv_apply, h4]
  rw [hc]
  simp only [Nat.cast_ofNat]
  have he : Real.exp (-π * (4 ^ 2 * gq ((j.1 : ℝ) / 4) ((j.2 : ℝ) / 4) q) *
      (x / 16)) = Real.exp (-π * gq ((j.1 : ℝ) / 4) ((j.2 : ℝ) / 4) q * x) := by
    congr 1; ring
  rw [he]
  ring

/-- **Grouping by the norm**: the lattice series is `4 f(ix/32)`. -/
theorem tsum_latT_eq {x : ℝ} (hx : 0 < x) :
    ∑' p, latT x p = 4 * X0.fC (I * ((x / 32 : ℝ) : ℂ)) := by
  set τ : UpperHalfPlane := ⟨I * ((x / 32 : ℝ) : ℂ), by simp; positivity⟩ with hτ
  have hη := ZInQ.GZTheta.etaThetaIdentity τ
  have hfib := (summable_latT hx).hasSum.tsum_fiberwise (fun p : ℤ × ℤ => (p.1 ^ 2 + p.2 ^ 2).toNat)
  have key : ∀ n : ℕ, ∑' p : ↑((fun p : ℤ × ℤ => (p.1 ^ 2 + p.2 ^ 2).toNat) ⁻¹' {n}), latT x p =
      4 * (heckeCoeff 1 n * cexp (2 * π * I * (τ : ℂ)) ^ n) := by
    intro n
    have hset : (fun p : ℤ × ℤ => (p.1 ^ 2 + p.2 ^ 2).toNat) ⁻¹' {n} = ↑(normFiber n) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe, mem_normFiber]
      have : 0 ≤ p.1 ^ 2 + p.2 ^ 2 := by positivity
      omega
    rw [hset, Finset.tsum_subtype' (normFiber n) (latT x)]
    have hw : cexp (2 * π * I * (τ : ℂ)) ^ n = ((Real.exp (-π * n * (x / 16)) : ℝ) : ℂ) := by
      rw [← Complex.exp_nat_mul, ofReal_exp]
      congr 1
      simp only [hτ, UpperHalfPlane.coe_mk]
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [hw, heckeCoeff, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hq : gq 0 0 p = (n : ℝ) := by
      have h := mem_normFiber.mp hp
      simp only [gq, add_zero]; exact_mod_cast h
    simp only [latT, hq, jacobiSym.one_right, Int.cast_one, one_mul]
    ring
  have hfib' : HasSum (fun n : ℕ => 4 * (heckeCoeff 1 n * cexp (2 * π * I * (τ : ℂ)) ^ n))
      (∑' p, latT x p) := hfib.congr_fun fun n => (key n).symm
  rw [hfib'.unique (hη.mul_left 4)]
  simp only [X0.fC, X0.etaD, hτ, UpperHalfPlane.coe_mk]
  push_cast
  ring

/-- **The theta kernel of `L(C₁, s)` is `¼ f(ix/32)`.** -/
theorem sum_cU_gaussTheta {x : ℝ} (hx : 0 < x) :
    ∑ j : Fin 4 × Fin 4, ZInQ.Contrib.TYZLcal.cU (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4)) *
      gaussTheta (((j.1 : ℝ) / 4 : ℝ) : UnitAddCircle) (((j.2 : ℝ) / 4 : ℝ) : UnitAddCircle) x =
      (1 / 4) * X0.fC (I * ((x / 32 : ℝ) : ℂ)) := by
  have h := (tsum_latT_block hx).symm.trans (tsum_latT_eq hx)
  have e : ∑ j : Fin 4 × Fin 4, ZInQ.Contrib.TYZLcal.cU (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4)) *
      gaussTheta (((j.1 : ℝ) / 4 : ℝ) : UnitAddCircle) (((j.2 : ℝ) / 4 : ℝ) : UnitAddCircle) x =
      (1 / 16) * ∑ j : Fin 4 × Fin 4, 4 * unitOf (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4)) *
      gaussTheta (((j.1 : ℝ) / 4 : ℝ) : UnitAddCircle) (((j.2 : ℝ) / 4 : ℝ) : UnitAddCircle) x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ZInQ.Contrib.TYZLcal.cU]
    ring
  rw [e, h]
  ring

theorem gaussLambda_one (a b : UnitAddCircle) :
    gaussLambda a b 1 = ∫ t in Ioi (0 : ℝ), gaussTheta a b t := by
  simp [gaussLambda, mellin]

theorem integrableOn_gaussTheta (a b : UnitAddCircle) :
    IntegrableOn (gaussTheta a b) (Ioi (0 : ℝ)) := by
  have h := mellinConvergent_gaussTheta a b 1
  simpa [MellinConvergent] using h

/-- **`L(C₁, 1) = 2π ∫₀^∞ f(it) dt`.** -/
theorem lValOne_one_eq_integral :
    ZInQ.Contrib.TYZDecomp.lValOne 1 = 2 * π * ∫ t in Ioi (0 : ℝ), X0.fC (I * t) := by
  rw [ZInQ.Contrib.TYZLcal.lValOne_one_eq]
  simp_rw [gaussLambda_one]
  have e1 : ∀ j : Fin 4 × Fin 4,
      ZInQ.Contrib.TYZLcal.cU (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4)) * (1 / 4) *
        ((π : ℂ) * ∫ t in Ioi (0 : ℝ),
          gaussTheta (((j.1 : ℝ) / 4 : ℝ) : UnitAddCircle) (((j.2 : ℝ) / 4 : ℝ) : UnitAddCircle) t) =
      (π / 4 : ℂ) * ∫ t in Ioi (0 : ℝ),
        ZInQ.Contrib.TYZLcal.cU (((j.1 : ℤ) : ZMod 4), ((j.2 : ℤ) : ZMod 4)) *
          gaussTheta (((j.1 : ℝ) / 4 : ℝ) : UnitAddCircle) (((j.2 : ℝ) / 4 : ℝ) : UnitAddCircle) t := by
    intro j
    rw [MeasureTheory.integral_const_mul]
    ring
  simp_rw [e1]
  rw [← Finset.mul_sum, ← MeasureTheory.integral_finsetSum]
  swap
  · intro j _
    exact (integrableOn_gaussTheta _ _).const_mul _
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => sum_cU_gaussTheta hx]
  rw [MeasureTheory.integral_const_mul]
  have hs := MeasureTheory.integral_comp_mul_left_Ioi (fun t : ℝ => X0.fC (I * t)) 0
    (b := 1 / 32) (by norm_num)
  simp only [mul_zero] at hs
  have e2 : (fun x : ℝ => X0.fC (I * ((x / 32 : ℝ) : ℂ))) =
      fun x : ℝ => X0.fC (I * ((1 / 32 * x : ℝ) : ℂ)) := by
    funext x; congr 3; ring
  rw [e2, hs, Complex.real_smul]
  push_cast
  ring

/-! ## The result -/

theorem lValOne_one : ZInQ.Contrib.TYZDecomp.lValOne 1 = (omegaInt : ℂ) / 4 := by
  rw [lValOne_one_eq_integral]
  have e : ∫ t in Ioi (0 : ℝ), X0.fC (I * t) = ∫ t in Ioi (0 : ℝ), ((Fr t : ℝ) : ℂ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    exact (Fr_eq t).symm
  rw [e, integral_complex_ofReal, integral_Fr]
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- **`𝓛(1) = 1`**: `L(y² = x³ − x, 1) = ¼ ∫₁^∞ dx/√(x³ − x)`. -/
theorem tyzLcalOne_proof : ZInQ.Contrib.TYZDecomp.TYZLcalOne := by
  unfold ZInQ.Contrib.TYZDecomp.TYZLcalOne
  rw [ZInQ.Contrib.TYZLcal.lcalSq_one, lValOne_one]
  have h : (omegaInt : ℂ) ≠ 0 := ofReal_ne_zero.mpr ZInQ.Contrib.TYZDecomp.omegaInt_pos.ne'
  field_simp

/-- **TYZ Theorem 1.1 (integrality) from TYZ Theorem 2.1 alone** (complex sign choices; tyz-genus's
`tyzThm11Integral_of_thm21C` with `TYZLcalOne` proved). -/
theorem tyzThm11Integral_of_thm21C_only (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC) :
    ZInQ.Contrib.TYZDecomp.TYZThm11Integral :=
  ZInQ.Contrib.TYZGenusFold.tyzThm11Integral_of_thm21C h21C tyzLcalOne_proof

end ZInQ.Contrib.LcalOne
