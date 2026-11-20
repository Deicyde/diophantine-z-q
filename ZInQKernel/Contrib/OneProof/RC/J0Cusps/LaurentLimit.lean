import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! The regular part of a convergent Laurent expansion takes the value of
its constant coefficient at the closed point. On the spot (c), tex
1785–1787 and 2937–2939. -/

noncomputable section

open Filter
open scoped Topology

namespace ZInQ.Manuscript.RC.J0Cusps

/-- Convergence of a power series at a single nonzero point gives an analytic
sum at zero, with the stated value there. The sum uses the bilateral indexing
of the Laurent inclusion. -/
theorem powerSeries_analytic_sum {K : Type} [Field K] (ι : K →+* ℂ)
    (P : PowerSeries K) {q t : ℂ} (hq : q ≠ 0)
    (h : HasSum (fun m : ℤ => ι ((P : LaurentSeries K).coeff m) * q ^ m) t) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = ι (PowerSeries.constantCoeff P) ∧
      ∀ᶠ z in 𝓝 (0 : ℂ),
        HasSum (fun m : ℤ => ι ((P : LaurentSeries K).coeff m) * z ^ m) (g z) := by
  have hzero (z : ℂ) (m : ℤ) (hm : m ∉ Set.range ((↑) : ℕ → ℤ)) :
      ι ((P : LaurentSeries K).coeff m) * z ^ m = 0 := by
    have hn : m < 0 := by
      contrapose! hm
      exact ⟨m.toNat, Int.toNat_of_nonneg hm⟩
    simp [PowerSeries.coeff_coe, hn]
  have hsum (z v : ℂ) :
      HasSum (fun m : ℤ => ι ((P : LaurentSeries K).coeff m) * z ^ m) v ↔
        HasSum (fun n : ℕ => ι (PowerSeries.coeff n P) * z ^ n) v := by
    simpa only [Function.comp_def, LaurentSeries.coeff_coe_powerSeries, zpow_natCast] using
      (Function.Injective.hasSum_iff (f := fun m : ℤ => ι ((P : LaurentSeries K).coeff m) * z ^ m)
        (fun _ _ h => by exact_mod_cast h) (hzero z) (a := v)).symm
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => ι (PowerSeries.coeff n P))
  have hp : 0 < p.radius := by
    refine lt_of_lt_of_le (b := (‖q‖₊ : ENNReal)) (by simpa using norm_pos_iff.mpr hq) ?_
    apply FormalMultilinearSeries.le_radius_of_tendsto (l := 0)
    convert tendsto_norm.comp ((hsum q t).mp h).summable.tendsto_atTop_zero using 1
    · funext n
      simp [p, norm_pow]
    · simp
  have hg := (p.hasFPowerSeriesOnBall hp).hasFPowerSeriesAt
  have hP : ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => ι (PowerSeries.coeff n P) * z ^ n) (p.sum z) := by
    simpa only [zero_add, p, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm]
      using hasFPowerSeriesAt_iff.mp hg
  refine ⟨p.sum, hg.analyticAt, ?_, hP.mono fun z hz => (hsum z _).mpr hz⟩
  have h0 := hasSum_single (f := fun n : ℕ => ι (PowerSeries.coeff n P) * (0 : ℂ) ^ n)
    0 (fun n hn => by simp [zero_pow hn])
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hP.self_of_nhds.unique h0

/-- The evaluation limit of a regular Laurent branch, along any filter on
which the chosen local parameter goes to zero. -/
theorem tendsto_powerSeries_eval {I K : Type} [Field K] {F : Filter I} [F.NeBot]
    (ι : K →+* ℂ) (P : PowerSeries K) (q g : I → ℂ)
    (hq : Tendsto q F (𝓝 0)) (hne : ∀ᶠ i in F, q i ≠ 0)
    (hs : ∀ᶠ i in F, HasSum (fun m : ℤ => ι ((P : LaurentSeries K).coeff m) * q i ^ m) (g i)) :
    Tendsto g F (𝓝 (ι (PowerSeries.constantCoeff P))) := by
  obtain ⟨i, hi, hi'⟩ := (hne.and hs).exists
  obtain ⟨f, hf, h0, he⟩ := powerSeries_analytic_sum ι P hi hi'
  rw [← h0]
  apply (hf.continuousAt.tendsto.comp hq).congr'
  filter_upwards [hs, hq.eventually he] with j hj hj'
  exact hj'.unique hj


end ZInQ.Manuscript.RC.J0Cusps
