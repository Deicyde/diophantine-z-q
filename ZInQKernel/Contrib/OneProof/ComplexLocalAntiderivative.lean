import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic

/-! An analytic complex function has a local holomorphic antiderivative. -/

noncomputable section

open Classical FormalMultilinearSeries
open scoped ENNReal NNReal

namespace AnalyticAt

/-- Integrating the convergent Taylor series yields a holomorphic primitive
in a neighborhood of the chosen point. -/
theorem exists_complex_antiderivative {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) :
    ∃ (g : ℂ → ℂ) (r : ℝ≥0∞), 0 < r ∧
      ∀ z ∈ Metric.eball x r, AnalyticAt ℂ g z ∧ HasDerivAt g (f z) z := by
  obtain ⟨p, r₀, hp⟩ := hf
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  let a : ℕ → ℂ
    | 0 => 0
    | n + 1 => p.coeff n / (n + 1 : ℕ)
  let q := FormalMultilinearSeries.ofScalars ℂ a
  obtain ⟨b, hb, C, hC, hbound⟩ :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (hr.trans_le hp.r_le)
  have hnorm (n : ℕ) : ‖q (n + 1)‖ ≤ ‖p n‖ := by
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef,
      FormalMultilinearSeries.norm_apply_eq_norm_coef (p := p)]
    change ‖(FormalMultilinearSeries.ofScalars ℂ a).coeff (n + 1)‖ ≤ _
    rw [coeff_ofScalars, norm_div, Complex.norm_natCast]
    exact div_le_self (norm_nonneg _) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have hqrad : (r : ℝ≥0∞) ≤ q.radius := by
    apply q.le_radius_of_bound (C * (r : ℝ))
    rintro (_ | n)
    · simpa [q, a] using (mul_nonneg hC.le r.coe_nonneg)
    · rw [pow_succ, ← mul_assoc]
      have hn : ‖p n‖ * (r : ℝ) ^ n ≤ C := (hbound n).trans
        ((mul_le_mul_of_nonneg_left (pow_le_one₀ hb.1.le hb.2.le) hC.le).trans_eq (mul_one _))
      exact mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_right (hnorm n) (by positivity)).trans hn) (by positivity)
  let g : ℂ → ℂ := fun z => q.sum (z - x)
  have hG : HasFPowerSeriesOnBall g q x (r : ℝ≥0∞) := by
    have h := (q.hasFPowerSeriesOnBall (hr0.trans_le hqrad)).comp_sub x
    simpa only [zero_add] using h.mono hr0 hqrad
  let eval : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ 1
  let q' := eval.compFormalMultilinearSeries q.derivSeries
  have hder : HasFPowerSeriesOnBall (deriv g) q' x (r : ℝ≥0∞) :=
    eval.comp_hasFPowerSeriesOnBall hG.fderiv
  have heq : q' = p := by
    ext n
    have hc : q'.coeff n = p.coeff n := by
      change q.derivSeries.coeff n 1 = _
      rw [FormalMultilinearSeries.derivSeries_coeff_one]
      change (n + 1) • (FormalMultilinearSeries.ofScalars ℂ a).coeff (n + 1) = _
      rw [coeff_ofScalars, nsmul_eq_mul]
      change (↑(n + 1 : ℕ) : ℂ) * (p.coeff n / ↑(n + 1 : ℕ)) = p.coeff n
      field_simp
    rw [← mkPiRing_coeff_eq q' n, ← mkPiRing_coeff_eq p n, hc]
  refine ⟨g, r, hr0, fun z hz => ?_⟩
  have hAn := hG.analyticOnNhd z hz
  have hdf := hAn.differentiableAt.hasDerivAt
  rw [heq] at hder
  have hdz := (hder.hasSum_sub hz).unique (hp.hasSum_sub (Metric.eball_subset_eball hr.le hz))
  exact ⟨hAn, hdz ▸ hdf⟩

end AnalyticAt

#print axioms AnalyticAt.exists_complex_antiderivative
