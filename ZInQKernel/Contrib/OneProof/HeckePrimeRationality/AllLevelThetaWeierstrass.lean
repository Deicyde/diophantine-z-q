import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaMultiplicationTwo
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Weierstrass normalization of the completed theta logarithmic derivative

The period pair is `(1, τ)` and its Weierstrass function is the actual lattice sum.
Local cancellation uses the divided difference of the actual completed theta.
The finite-part constant is defined by an actual derivative of its analytic unit.
-/

noncomputable section
set_option autoImplicit false

open Complex Set Filter Function
open scoped Topology Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.ThetaWeierstrass

open ZInQ.Contrib.HeckePrimeRationality

/-- The actual period pair with periods `1` and `τ`. -/
def periodPair (τ : _root_.UpperHalfPlane) : _root_.PeriodPair where
  ω₁ := 1
  ω₂ := (τ : ℂ)
  indep := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have him := congrArg Complex.im hab
    have hre := congrArg Complex.re hab
    simp at him hre
    have hb : b = 0 := him.resolve_right τ.im_ne_zero
    exact ⟨by simpa [hb] using hre, hb⟩

theorem mem_periodPair_lattice_iff (τ : _root_.UpperHalfPlane) (z : _root_.Complex) :
    z ∈ (periodPair τ).lattice ↔ ∃ m n : _root_.Int, z = (m : ℂ) + (n : ℂ) * (τ : ℂ) := by
  rw [PeriodPair.mem_lattice]
  simp only [periodPair, mul_one]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, h.symm⟩
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, h.symm⟩

theorem H_zero_iff_mem_lattice (τ : _root_.UpperHalfPlane) (z : _root_.Complex) :
    CompletedTheta.H τ z = 0 ↔ z ∈ (periodPair τ).lattice := by
  rw [CompletedTheta.H_zero_iff_lattice, mem_periodPair_lattice_iff]

theorem H_ne_zero_of_notMem (τ : _root_.UpperHalfPlane) {z : _root_.Complex}
    (hz : z ∉ (periodPair τ).lattice) : CompletedTheta.H τ z ≠ 0 := by
  exact fun h => hz ((H_zero_iff_mem_lattice τ z).mp h)

theorem deriv_H_ne_zero_of_mem (τ : _root_.UpperHalfPlane) {z : _root_.Complex}
    (hz : z ∈ (periodPair τ).lattice) : deriv (CompletedTheta.H τ) z ≠ 0 := by
  exact QuasiThetaMultiplicationTwo.deriv_ne_zero_at_zero (CompletedTheta.differentiable_H τ)
    (CompletedTheta.H_add_one τ)
    (fun w => by simpa only [neg_mul, mul_assoc] using CompletedTheta.H_add_tau τ w)
    (CompletedTheta.H_zero_iff_lattice τ) (CompletedTheta.deriv_H_zero_ne_zero τ)
    ((H_zero_iff_mem_lattice τ z).mpr hz)

/-- The genuine logarithmic derivative, with division only used off its zero set. -/
def logDerivative (F : _root_.Complex → _root_.Complex) (z : _root_.Complex) : _root_.Complex :=
  deriv F z / F z

/-- The analytic part of a logarithmic derivative after removing its simple pole at `c`. -/
def unitLogDerivative (F : _root_.Complex → _root_.Complex) (c z : _root_.Complex) : _root_.Complex :=
  logDerivative (dslope F c) z

theorem analyticAt_logDerivative {F : _root_.Complex → _root_.Complex}
    (hF : Differentiable ℂ F) {z : _root_.Complex} (hz : F z ≠ 0) :
    AnalyticAt ℂ (logDerivative F) z := by
  exact (hF.analyticAt z).deriv.div (hF.analyticAt z) hz

theorem factor_dslope {F : _root_.Complex → _root_.Complex} {c : _root_.Complex}
    (hc : F c = 0) (z : _root_.Complex) : F z = (z - c) * dslope F c z := by
  simpa only [smul_eq_mul, hc, sub_zero] using (sub_smul_dslope F c z).symm

theorem deriv_factor_dslope {F : _root_.Complex → _root_.Complex} {c : _root_.Complex}
    (hF : Differentiable ℂ F) (hc : F c = 0) (z : _root_.Complex) :
    deriv F z = dslope F c z + (z - c) * deriv (dslope F c) z := by
  have hA := QuasiThetaMultiplicationTwo.differentiable_dslope hF c
  have hp : HasDerivAt F (1 * dslope F c z + (z - c) * deriv (dslope F c) z) z := by
    exact (((hasDerivAt_id z).sub_const c).mul (hA z).hasDerivAt).congr_of_eventuallyEq
      (Eventually.of_forall (factor_dslope hc))
  simpa only [one_mul] using! hp.deriv

/-- The exact simple-pole splitting, not an asymptotic assumption. -/
theorem logDerivative_eq_inv_add_unit {F : _root_.Complex → _root_.Complex} {c z : _root_.Complex}
    (hF : Differentiable ℂ F) (hc : F c = 0) (hz : z ≠ c) (hAz : dslope F c z ≠ 0) :
    logDerivative F z = 1 / (z - c) + unitLogDerivative F c z := by
  rw [logDerivative, deriv_factor_dslope hF hc, factor_dslope hc, unitLogDerivative,
    logDerivative]
  field_simp [sub_ne_zero.mpr hz, hAz]

/-- Differentiating the splitting removes exactly the double principal part. -/
theorem deriv_logDerivative_eq_neg_inv_sq_add {F : _root_.Complex → _root_.Complex}
    {c z : _root_.Complex} (hF : Differentiable ℂ F) (hc : F c = 0) (hz : z ≠ c)
    (hAz : dslope F c z ≠ 0) :
    deriv (logDerivative F) z = -(1 / (z - c) ^ 2) + deriv (unitLogDerivative F c) z := by
  have hA := QuasiThetaMultiplicationTwo.differentiable_dslope hF c
  have hu : AnalyticAt ℂ (unitLogDerivative F c) z := analyticAt_logDerivative hA hAz
  have hnear : logDerivative F =ᶠ[𝓝 z]
      (fun w : ℂ => 1 / (w - c) + unitLogDerivative F c w) := by
    filter_upwards [continuousAt_id.eventually_ne hz, (hA z).continuousAt.eventually_ne hAz]
      with w hw hAw
    exact logDerivative_eq_inv_add_unit hF hc hw hAw
  rw [hnear.deriv_eq]
  have hi : HasDerivAt (fun w : ℂ => 1 / (w - c)) (-(1 / (z - c) ^ 2)) z := by
    simpa only [one_div, Pi.inv_apply, neg_div] using!
      ((hasDerivAt_id z).sub_const c).inv (sub_ne_zero.mpr hz)
  simpa using! (hi.add hu.differentiableAt.hasDerivAt).deriv

/-- The actual completed theta divided by its zero at the origin, with its analytic value there. -/
def dividedTheta (τ : _root_.UpperHalfPlane) : _root_.Complex → _root_.Complex :=
  dslope (CompletedTheta.H τ) 0

/-- The finite-part constant determined by the actual analytic unit at the origin. -/
def finitePart (τ : _root_.UpperHalfPlane) : _root_.Complex :=
  deriv (unitLogDerivative (CompletedTheta.H τ) 0) 0

theorem differentiable_dividedTheta (τ : _root_.UpperHalfPlane) :
    Differentiable ℂ (dividedTheta τ) :=
  QuasiThetaMultiplicationTwo.differentiable_dslope (CompletedTheta.differentiable_H τ) 0

theorem dividedTheta_zero (τ : _root_.UpperHalfPlane) :
    dividedTheta τ 0 = deriv (CompletedTheta.H τ) 0 := by
  simp [dividedTheta]

theorem dividedTheta_zero_ne_zero (τ : _root_.UpperHalfPlane) : dividedTheta τ 0 ≠ 0 := by
  rw [dividedTheta_zero]
  exact CompletedTheta.deriv_H_zero_ne_zero τ

theorem dividedTheta_even (τ : _root_.UpperHalfPlane) : Function.Even (dividedTheta τ) := by
  intro z
  by_cases hz : z = 0
  · subst z
    simp
  · rw [dividedTheta, dslope_of_ne _ (neg_ne_zero.mpr hz), dslope_of_ne _ hz]
    simp [slope, smul_eq_mul, CompletedTheta.H_zero, CompletedTheta.H_neg]

theorem deriv_dividedTheta_zero (τ : _root_.UpperHalfPlane) : deriv (dividedTheta τ) 0 = 0 := by
  have heq : (fun z : ℂ => dividedTheta τ (-z)) = dividedTheta τ :=
    funext (dividedTheta_even τ)
  have h := deriv_comp_neg (dividedTheta τ) 0
  rw [heq, neg_zero] at h
  linear_combination h / 2

theorem unitLogDerivative_zero (τ : _root_.UpperHalfPlane) :
    unitLogDerivative (CompletedTheta.H τ) 0 0 = 0 := by
  change deriv (dividedTheta τ) 0 / dividedTheta τ 0 = 0
  rw [deriv_dividedTheta_zero, zero_div]

theorem analyticAt_unitLogDerivative_zero (τ : _root_.UpperHalfPlane) :
    AnalyticAt ℂ (unitLogDerivative (CompletedTheta.H τ) 0) 0 :=
  analyticAt_logDerivative (differentiable_dividedTheta τ) (dividedTheta_zero_ne_zero τ)

/-- A punctured-neighborhood Laurent splitting for the actual completed theta. -/
theorem H_logDerivative_laurent (τ : _root_.UpperHalfPlane) :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
      deriv (CompletedTheta.H τ) z / CompletedTheta.H τ z =
        1 / z + unitLogDerivative (CompletedTheta.H τ) 0 z := by
  have hA := differentiable_dividedTheta τ
  have hn := (hA 0).continuousAt.eventually_ne (dividedTheta_zero_ne_zero τ)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzne
  simpa [logDerivative] using! logDerivative_eq_inv_add_unit (CompletedTheta.differentiable_H τ)
    (CompletedTheta.H_zero τ) hzne hz

/-- The finite part of the negative derivative is the negative actual constant `finitePart τ`. -/
theorem H_neg_logDerivative_finitePart (τ : _root_.UpperHalfPlane) :
    Tendsto (fun z : ℂ => -(deriv (fun w : ℂ => deriv (CompletedTheta.H τ) w /
      CompletedTheta.H τ w) z) - 1 / z ^ 2) (𝓝[≠] (0 : ℂ)) (𝓝 (-finitePart τ)) := by
  have hA := differentiable_dividedTheta τ
  have hn := (hA 0).continuousAt.eventually_ne (dividedTheta_zero_ne_zero τ)
  have hlocal : (fun z : ℂ => -(deriv (logDerivative (CompletedTheta.H τ)) z) - 1 / z ^ 2) =ᶠ[
      𝓝[≠] (0 : ℂ)] (fun z => -deriv (unitLogDerivative (CompletedTheta.H τ) 0) z) := by
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzne
    rw [deriv_logDerivative_eq_neg_inv_sq_add (CompletedTheta.differentiable_H τ)
      (CompletedTheta.H_zero τ) hzne hz]
    simp
  have ht : Tendsto (fun z : ℂ => -deriv (unitLogDerivative (CompletedTheta.H τ) 0) z)
      (𝓝[≠] (0 : ℂ)) (𝓝 (-finitePart τ)) :=
    (analyticAt_unitLogDerivative_zero τ).deriv.continuousAt.neg.tendsto.mono_left
      nhdsWithin_le_nhds
  exact ht.congr' hlocal.symm

/-- The actual lattice sum has the normalized double principal part and an analytic remainder. -/
theorem weierstrassP_eq_principal_part (τ : _root_.UpperHalfPlane) (z : _root_.Complex) :
    (periodPair τ).weierstrassP z = 1 / z ^ 2 + (periodPair τ).weierstrassPExcept 0 z := by
  simpa [add_comm] using ((periodPair τ).weierstrassPExcept_add (0 : (periodPair τ).lattice) z).symm

theorem analyticAt_weierstrass_regular_part (τ : _root_.UpperHalfPlane) :
    AnalyticAt ℂ ((periodPair τ).weierstrassPExcept 0) 0 :=
  (periodPair τ).analyticAt_weierstrassPExcept 0

theorem weierstrass_regular_part_zero (τ : _root_.UpperHalfPlane) :
    (periodPair τ).weierstrassPExcept 0 0 = 0 := by simp

/-- The finite part of the actual Weierstrass lattice sum at zero is zero. -/
theorem weierstrassP_finitePart_zero (τ : _root_.UpperHalfPlane) :
    Tendsto (fun z : ℂ => (periodPair τ).weierstrassP z - 1 / z ^ 2)
      (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
  have heq : (fun z : ℂ => (periodPair τ).weierstrassP z - 1 / z ^ 2) =
      (periodPair τ).weierstrassPExcept 0 := by
    funext z
    rw [weierstrassP_eq_principal_part]
    ring
  rw [heq]
  have ht : Tendsto ((periodPair τ).weierstrassPExcept 0) (𝓝[≠] (0 : ℂ))
      (𝓝 ((periodPair τ).weierstrassPExcept 0 0)) :=
    (analyticAt_weierstrass_regular_part τ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [weierstrass_regular_part_zero] using ht

/-! ## Cancellation against the actual Weierstrass lattice sum -/

/-- The comparison has explicit analytic values at the former poles. -/
def comparison (τ : _root_.UpperHalfPlane) (z : _root_.Complex) : _root_.Complex :=
  if CompletedTheta.H τ z = 0 then
    deriv (unitLogDerivative (CompletedTheta.H τ) z) z - finitePart τ
  else
    (periodPair τ).weierstrassP z + deriv (logDerivative (CompletedTheta.H τ)) z - finitePart τ

theorem weierstrassPExcept_self (τ : _root_.UpperHalfPlane) {z : _root_.Complex}
    (hz : z ∈ (periodPair τ).lattice) : (periodPair τ).weierstrassPExcept z z = 1 / z ^ 2 := by
  have h := (periodPair τ).weierstrassPExcept_add ⟨z, hz⟩ z
  rw [(periodPair τ).weierstrassP_coe ⟨z, hz⟩] at h
  simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), div_zero, zero_sub] at h
  linear_combination h

/-- The double poles cancel locally at every actual theta zero. -/
theorem analyticAt_comparison (τ : _root_.UpperHalfPlane) (z : _root_.Complex) :
    AnalyticAt ℂ (comparison τ) z := by
  classical
  have hH := CompletedTheta.differentiable_H τ
  by_cases hz : CompletedTheta.H τ z = 0
  · have hzL := (H_zero_iff_mem_lattice τ z).mp hz
    have hd := deriv_H_ne_zero_of_mem τ hzL
    have hA := QuasiThetaMultiplicationTwo.differentiable_dslope hH z
    have hAz : dslope (CompletedTheta.H τ) z z ≠ 0 := by simpa only [dslope_same] using hd
    have hu : AnalyticAt ℂ (unitLogDerivative (CompletedTheta.H τ) z) z :=
      analyticAt_logDerivative hA hAz
    have hG : AnalyticAt ℂ (fun w : ℂ => (periodPair τ).weierstrassPExcept z w - 1 / z ^ 2 +
        deriv (unitLogDerivative (CompletedTheta.H τ) z) w - finitePart τ) z := by
      exact (((periodPair τ).analyticAt_weierstrassPExcept z).sub analyticAt_const).add hu.deriv
        |>.sub analyticAt_const
    have heq : comparison τ =ᶠ[𝓝 z] (fun w : ℂ => (periodPair τ).weierstrassPExcept z w -
        1 / z ^ 2 + deriv (unitLogDerivative (CompletedTheta.H τ) z) w - finitePart τ) := by
      filter_upwards [(hA z).continuousAt.eventually_ne hAz] with w hAw
      by_cases hw : w = z
      · subst w
        simp [comparison, hz, weierstrassPExcept_self τ hzL]
      · have hHw : CompletedTheta.H τ w ≠ 0 := by
          rw [factor_dslope hz]
          exact mul_ne_zero (sub_ne_zero.mpr hw) hAw
        rw [comparison, ite_eq_right hHw,
          deriv_logDerivative_eq_neg_inv_sq_add hH hz hw hAw,
          ← (periodPair τ).weierstrassPExcept_add ⟨z, hzL⟩ w]
        ring
    exact hG.congr heq.symm
  · have hzL : z ∉ (periodPair τ).lattice := by
      exact fun h => hz ((H_zero_iff_mem_lattice τ z).mpr h)
    have hP := (periodPair τ).analyticOnNhd_weierstrassP z hzL
    have hlog := (analyticAt_logDerivative hH hz).deriv
    have hG : AnalyticAt ℂ (fun w : ℂ => (periodPair τ).weierstrassP w +
        deriv (logDerivative (CompletedTheta.H τ)) w - finitePart τ) z :=
      (hP.add hlog).sub analyticAt_const
    apply hG.congr
    filter_upwards [(hH z).continuousAt.eventually_ne hz] with w hw
    simp [comparison, hw]

theorem comparison_zero (τ : _root_.UpperHalfPlane) : comparison τ 0 = 0 := by
  simp [comparison, CompletedTheta.H_zero, finitePart]

local notation "κ" => ((Real.pi : ℂ) * Complex.I)

/-- The actual logarithmic derivative is periodic under the unit period. -/
theorem H_logDerivative_add_one (τ : _root_.UpperHalfPlane) (z : _root_.Complex) :
    logDerivative (CompletedTheta.H τ) (z + 1) = logDerivative (CompletedTheta.H τ) z := by
  change deriv (CompletedTheta.H τ) (z + 1) / CompletedTheta.H τ (z + 1) =
    deriv (CompletedTheta.H τ) z / CompletedTheta.H τ z
  rw [QuasiThetaMultiplicationTwo.deriv_add_one (CompletedTheta.differentiable_H τ)
    (CompletedTheta.H_add_one τ), CompletedTheta.H_add_one]
  simp

theorem H_deriv_logDerivative_add_one (τ : _root_.UpperHalfPlane) (z : _root_.Complex) :
    deriv (logDerivative (CompletedTheta.H τ)) (z + 1) =
      deriv (logDerivative (CompletedTheta.H τ)) z := by
  have h := congrArg (fun f : ℂ → ℂ => deriv f z) (funext (H_logDerivative_add_one τ))
  simpa only [deriv_comp_add_const] using! h

/-- The actual theta quasi-period gives its full derivative transformation. -/
theorem H_deriv_add_tau (τ : _root_.UpperHalfPlane) (z : _root_.Complex) :
    deriv (CompletedTheta.H τ) (z + (τ : ℂ)) =
      -cexp (-κ * (τ : ℂ) - 2 * κ * z) *
        (deriv (CompletedTheta.H τ) z - 2 * κ * CompletedTheta.H τ z) := by
  have hH := CompletedTheta.differentiable_H τ
  have ha : HasDerivAt (fun w : ℂ => CompletedTheta.H τ (w + (τ : ℂ)))
      (deriv (CompletedTheta.H τ) (z + (τ : ℂ))) z :=
    HasDerivAt.comp_add_const z (τ : ℂ) (hH (z + (τ : ℂ))).hasDerivAt
  have he : HasDerivAt (fun w : ℂ => -κ * (τ : ℂ) - 2 * κ * w) (-2 * κ) z := by
    convert! ((hasDerivAt_id z).const_mul (-2 * κ)).const_add (-κ * (τ : ℂ)) using 1
    · funext w
      simp only [id_eq]
      ring
    · ring
  have hb := (he.cexp.neg.mul (hH z).hasDerivAt).congr_of_eventuallyEq
    (Eventually.of_forall (fun w => by
      simpa only [Pi.mul_apply, Pi.neg_apply, neg_mul, mul_assoc] using CompletedTheta.H_add_tau τ w))
  have hi := ha.unique hb
  simp only [Pi.neg_apply] at hi
  linear_combination hi

/-- Off the zero set, the logarithmic quasi-period is an additive constant. -/
theorem H_logDerivative_add_tau (τ : _root_.UpperHalfPlane) {z : _root_.Complex}
    (hz : CompletedTheta.H τ z ≠ 0) :
    logDerivative (CompletedTheta.H τ) (z + (τ : ℂ)) =
      logDerivative (CompletedTheta.H τ) z - 2 * κ := by
  change deriv (CompletedTheta.H τ) (z + (τ : ℂ)) / CompletedTheta.H τ (z + (τ : ℂ)) =
    deriv (CompletedTheta.H τ) z / CompletedTheta.H τ z - 2 * κ
  rw [H_deriv_add_tau]
  have ht : CompletedTheta.H τ (z + (τ : ℂ)) =
      -cexp (-κ * (τ : ℂ) - 2 * κ * z) * CompletedTheta.H τ z := by
    simpa only [neg_mul, mul_assoc] using CompletedTheta.H_add_tau τ z
  rw [ht]
  field_simp [hz, Complex.exp_ne_zero]

/-- Differentiating removes the additive logarithmic quasi-period, off lattice. -/
theorem H_deriv_logDerivative_add_tau (τ : _root_.UpperHalfPlane) {z : _root_.Complex}
    (hz : CompletedTheta.H τ z ≠ 0) :
    deriv (logDerivative (CompletedTheta.H τ)) (z + (τ : ℂ)) =
      deriv (logDerivative (CompletedTheta.H τ)) z := by
  have heq : (fun w : ℂ => logDerivative (CompletedTheta.H τ) (w + (τ : ℂ))) =ᶠ[𝓝 z]
      (fun w => logDerivative (CompletedTheta.H τ) w - 2 * κ) := by
    filter_upwards [(CompletedTheta.differentiable_H τ z).continuousAt.eventually_ne hz] with w hw
    exact H_logDerivative_add_tau τ hw
  simpa only [deriv_comp_add_const, deriv_sub_const] using! heq.deriv_eq

theorem comparison_add_one_off_zero (τ : _root_.UpperHalfPlane) {z : _root_.Complex}
    (hz : CompletedTheta.H τ z ≠ 0) : comparison τ (z + 1) = comparison τ z := by
  have hz1 : CompletedTheta.H τ (z + 1) ≠ 0 := by
    rw [CompletedTheta.H_add_one]
    exact neg_ne_zero.mpr hz
  have hP : (periodPair τ).weierstrassP (z + 1) = (periodPair τ).weierstrassP z :=
    (periodPair τ).weierstrassP_add_coe z ⟨1, (periodPair τ).ω₁_mem_lattice⟩
  simp only [comparison, ite_eq_right hz, ite_eq_right hz1, hP, H_deriv_logDerivative_add_one]

theorem comparison_add_tau_off_zero (τ : _root_.UpperHalfPlane) {z : _root_.Complex}
    (hz : CompletedTheta.H τ z ≠ 0) : comparison τ (z + (τ : ℂ)) = comparison τ z := by
  have hzτ : CompletedTheta.H τ (z + (τ : ℂ)) ≠ 0 := by
    rw [CompletedTheta.H_add_tau]
    exact mul_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero _)) hz
  have hP : (periodPair τ).weierstrassP (z + (τ : ℂ)) = (periodPair τ).weierstrassP z :=
    (periodPair τ).weierstrassP_add_coe z ⟨(τ : ℂ), (periodPair τ).ω₂_mem_lattice⟩
  simp only [comparison, ite_eq_right hz, ite_eq_right hzτ, hP, H_deriv_logDerivative_add_tau τ hz]

/-- Continuity extends an independently proved off-zero period through simple lattice zeros. -/
theorem comparison_periodic_of_off_zero (τ : _root_.UpperHalfPlane) (p : _root_.Complex)
    (hoff : ∀ z : ℂ, CompletedTheta.H τ z ≠ 0 → comparison τ (z + p) = comparison τ z) :
    Function.Periodic (comparison τ) p := by
  have hQ : Differentiable ℂ (comparison τ) := fun z => (analyticAt_comparison τ z).differentiableAt
  intro c
  by_cases hc : CompletedTheta.H τ c = 0
  · have hn := QuasiThetaMultiplicationTwo.eventually_ne_zero_of_simple
      (CompletedTheta.differentiable_H τ c) hc
      (deriv_H_ne_zero_of_mem τ ((H_zero_iff_mem_lattice τ c).mp hc))
    have hleft : Tendsto (fun z : ℂ => comparison τ (z + p)) (𝓝[≠] c) (𝓝 (comparison τ (c + p))) :=
      (hQ.continuous.comp (continuous_id.add continuous_const)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have hright : Tendsto (comparison τ) (𝓝[≠] c) (𝓝 (comparison τ c)) :=
      (hQ c).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (hleft.congr' (hn.mono fun z hz => hoff z hz)) hright
  · exact hoff c hc

/-- The explicit comparison is entire and doubly periodic, hence its zero at the origin fixes it. -/
theorem comparison_eq_zero (τ : _root_.UpperHalfPlane) (z : _root_.Complex) : comparison τ z = 0 := by
  have hQ : Differentiable ℂ (comparison τ) := fun w => (analyticAt_comparison τ w).differentiableAt
  have h1 := comparison_periodic_of_off_zero τ 1 (fun w hw => comparison_add_one_off_zero τ hw)
  have ht := comparison_periodic_of_off_zero τ (τ : ℂ) (fun w hw => comparison_add_tau_off_zero τ hw)
  have hb := QuasiThetaMultiplicationTwo.bounded_of_continuous_periodic hQ.continuous h1 ht
  exact (hQ.apply_eq_apply_of_bounded hb z 0).trans (comparison_zero τ)

/-- The actual Weierstrass lattice sum is the normalized negative derivative of the actual
completed theta logarithmic derivative, off the actual lattice. -/
theorem weierstrassP_eq_neg_deriv_logDerivative (τ : _root_.UpperHalfPlane) (z : _root_.Complex)
    (hz : z ∉ (periodPair τ).lattice) :
    (periodPair τ).weierstrassP z =
      -(deriv (fun w : ℂ => deriv (CompletedTheta.H τ) w / CompletedTheta.H τ w) z) + finitePart τ := by
  have h := comparison_eq_zero τ z
  rw [comparison, ite_eq_right (H_ne_zero_of_notMem τ hz)] at h
  change (periodPair τ).weierstrassP z = -deriv (logDerivative (CompletedTheta.H τ)) z + finitePart τ
  linear_combination h

/-! ## The finite-part constant in terms of the actual third derivative -/

/-- The actual completed theta factors globally through its entire divided difference. -/
theorem H_eq_mul_dividedTheta (τ : _root_.UpperHalfPlane) :
    CompletedTheta.H τ = (fun z : ℂ => z * dividedTheta τ z) := by
  funext z
  simpa only [sub_zero, dividedTheta] using! factor_dslope (CompletedTheta.H_zero τ) z

/-- Differentiating the actual factorization three times fixes the coefficient normalization. -/
theorem iteratedDeriv_three_H_zero (τ : _root_.UpperHalfPlane) :
    iteratedDeriv 3 (CompletedTheta.H τ) 0 = 3 * iteratedDeriv 2 (dividedTheta τ) 0 := by
  rw [H_eq_mul_dividedTheta]
  rw [iteratedDeriv_fun_mul (by fun_prop)
    ((differentiable_dividedTheta τ).analyticAt 0).contDiffAt]
  simp [Finset.sum_range_succ, iteratedDeriv_fun_id]

theorem finitePart_eq_second_unit_derivative (τ : _root_.UpperHalfPlane) :
    finitePart τ = iteratedDeriv 2 (dividedTheta τ) 0 / dividedTheta τ 0 := by
  have hA := differentiable_dividedTheta τ
  have hAz := dividedTheta_zero_ne_zero τ
  have hd := (((hA.analyticAt 0).deriv.differentiableAt.hasDerivAt).div
    (hA 0).hasDerivAt hAz).deriv
  rw [deriv_dividedTheta_zero, mul_zero, sub_zero] at hd
  change deriv (fun z : ℂ => deriv (dividedTheta τ) z / dividedTheta τ z) 0 = _ at hd
  change deriv (fun z : ℂ => deriv (dividedTheta τ) z / dividedTheta τ z) 0 = _
  rw [hd, iteratedDeriv_succ, iteratedDeriv_one]
  field_simp [hAz]

/-- The finite-part constant is the actual `H'''(0)/(3 H'(0))`, not a supplied constant identity. -/
theorem finitePart_eq_third_derivative (τ : _root_.UpperHalfPlane) :
    finitePart τ = iteratedDeriv 3 (CompletedTheta.H τ) 0 / (3 * deriv (CompletedTheta.H τ) 0) := by
  rw [finitePart_eq_second_unit_derivative, iteratedDeriv_three_H_zero, ← dividedTheta_zero]
  field_simp [dividedTheta_zero_ne_zero τ]

/-- The actual off-lattice Weierstrass–theta identity, with its exact derivative normalization. -/
theorem weierstrassP_eq_theta_third_derivative (τ : _root_.UpperHalfPlane) (z : _root_.Complex)
    (hz : z ∉ (periodPair τ).lattice) :
    (periodPair τ).weierstrassP z =
      -(deriv (fun w : ℂ => deriv (CompletedTheta.H τ) w / CompletedTheta.H τ w) z) +
        iteratedDeriv 3 (CompletedTheta.H τ) 0 / (3 * deriv (CompletedTheta.H τ) 0) := by
  rw [← finitePart_eq_third_derivative]
  exact weierstrassP_eq_neg_deriv_logDerivative τ z hz

end ZInQ.Contrib.HeckePrimeRationality.ThetaWeierstrass
