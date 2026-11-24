import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue

/-! # height-dict: holomorphic maps of several variables are strictly differentiable

Mathlib 4.35 proves that a complex-differentiable function of one variable is `C^∞`
(`DifferentiableOn.contDiffOn`, for `f : ℂ → E`). This file proves the first-order statement in
several variables: if `f : ℂ^g → E` is `ℂ`-differentiable on an open set `U`, then `fderiv ℂ f` is
continuous on `U`, hence `f` is strictly differentiable there. Each partial derivative
`z ↦ fderiv ℂ f z v` is a Cauchy integral `(2πi)⁻¹ ∮_{|t| = R} t⁻² f(z + t v) dt`, which depends
continuously on `z`. -/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real

set_option linter.unusedSectionVars false

namespace ZInQ.HeightDict.Holomorphic

variable {g : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem continuousAt_fderiv {f : (Fin g → ℂ) → E} {U : Set (Fin g → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x₀ : Fin g → ℂ} (hx₀ : x₀ ∈ U) :
    ContinuousAt (fderiv ℂ f) x₀ := by
  obtain ⟨ρ', hρ', hρU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  set ρ := ρ' / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  rw [continuousAt_clm_apply]
  intro v
  by_cases hv : v = 0
  · subst hv; simp only [map_zero]; exact continuousAt_const
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set R := ρ / ‖v‖ with hRdef
  have hR : 0 < R := div_pos hρ hvpos
  -- the points `z + t v`
  have hmem : ∀ z ∈ ball x₀ ρ, ∀ t : ℂ, ‖t‖ ≤ R → z + t • v ∈ U := by
    intro z hz t ht
    apply hρU
    rw [mem_ball] at hz ⊢
    have h1 : ‖t • v‖ ≤ ρ := by
      rw [norm_smul]
      calc ‖t‖ * ‖v‖ ≤ R * ‖v‖ := mul_le_mul_of_nonneg_right ht hvpos.le
        _ = ρ := by rw [hRdef]; field_simp
    calc dist (z + t • v) x₀ = ‖(z - x₀) + t • v‖ := by rw [dist_eq_norm]; congr 1; abel
      _ ≤ ‖z - x₀‖ + ‖t • v‖ := norm_add_le _ _
      _ < ρ + ρ := by rw [← dist_eq_norm]; linarith
      _ = ρ' := by rw [hρdef]; ring
  -- Cauchy's formula for `t ↦ f (z + t v)`
  have hcauchy : ∀ z ∈ ball x₀ ρ, fderiv ℂ f z v =
      (2 * π * I)⁻¹ • ∮ t in C(0, R), (1 / (t - 0) ^ 2) • f (z + t • v) := by
    intro z hz
    have hd : DifferentiableOn ℂ (fun t : ℂ => f (z + t • v)) (closedBall 0 R) := by
      intro t ht
      have ht' : ‖t‖ ≤ R := by simpa using ht
      have h1 : DifferentiableAt ℂ f (z + t • v) := hf.differentiableAt (hU.mem_nhds (hmem z hz t ht'))
      have h2 : DifferentiableAt ℂ (fun t : ℂ => z + t • v) t :=
        (differentiableAt_const _).add (differentiableAt_id.smul_const v)
      exact (h1.comp t h2).differentiableWithinAt
    have hC := hd.deriv_eq_smul_circleIntegral hR
    have hderiv : deriv (fun t : ℂ => f (z + t • v)) 0 = fderiv ℂ f z v := by
      have h1 : HasFDerivAt f (fderiv ℂ f z) (z + (0 : ℂ) • v) := by
        rw [zero_smul, add_zero]
        exact (hf.differentiableAt (hU.mem_nhds (by
          have := hmem z hz 0 (by simp [hR.le]); simpa using this))).hasFDerivAt
      have h2 : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
      exact (h1.comp_hasDerivAt 0 h2).deriv
    rw [hC, hderiv, smul_smul, inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero] : (2 * (π : ℂ) * I) ≠ 0), one_smul]
  -- continuity of the Cauchy integral in `z`
  have hcont : ContinuousOn
      (fun z => (2 * π * I)⁻¹ • ∮ t in C(0, R), (1 / (t - 0) ^ 2) • f (z + t • v))
      (ball x₀ ρ) := by
    refine ContinuousOn.const_smul ?_ _
    rw [continuousOn_iff_continuous_domRestrict]
    simp only [circleIntegral]
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 (2 * π)
    have hfc : ContinuousOn f U := hf.continuousOn
    have hcm : Continuous (circleMap (0 : ℂ) R) := continuous_circleMap 0 R
    refine Continuous.smul ?_ (Continuous.smul ?_ ?_)
    · simp only [deriv_circleMap]
      exact (hcm.comp continuous_snd).mul continuous_const
    · refine Continuous.div continuous_const ((hcm.comp continuous_snd).sub continuous_const |>.pow 2)
        fun p => by simp [hR.ne']
    · refine hfc.comp_continuous ((continuous_subtype_val.comp continuous_fst).add
        ((hcm.comp continuous_snd).smul continuous_const)) fun p => ?_
      exact hmem p.1 p.1.2 _ (by simp [abs_of_pos hR])
  exact (hcont.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hρ))).congr
    (eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hρ))
      fun z hz => (hcauchy z hz).symm)

/-- **Holomorphic maps of several variables are strictly differentiable.** -/
theorem hasStrictFDerivAt {f : (Fin g → ℂ) → E} {U : Set (Fin g → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x₀ : Fin g → ℂ} (hx₀ : x₀ ∈ U) :
    HasStrictFDerivAt f (fderiv ℂ f x₀) x₀ :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (eventually_of_mem (hU.mem_nhds hx₀) fun y hy =>
      (hf.differentiableAt (hU.mem_nhds hy)).hasFDerivAt)
    (continuousAt_fderiv hU hf hx₀)

end ZInQ.HeightDict.Holomorphic
