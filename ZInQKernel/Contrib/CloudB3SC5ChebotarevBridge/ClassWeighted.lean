import ZInQKernel.Contrib.TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount
import ZInQKernel.Contrib.TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.IdealZetaSum
import ZInQKernel.Contrib.TauCeti.Analysis.SpecialFunctions.Log.OneDivSub

/-!
# Logarithmically normalized weighted Chebotarev bound

Uses the already-proved Tau Ceti Chebotarev theorem and its natural-to-Dirichlet
and logarithmic-normalization dictionaries, over genuine number-field primes.
No qualitative-density substitution and no new quantitative hypothesis.
The imported Tau Ceti source retains its Apache-2.0 copyright/credit notices.
-/

open Filter
open scoped Topology

namespace C5ChebotarevBridge

/-- The class prime sum divided by `log (1 / (s - 1))` has its exact
Chebotarev limit. -/
theorem class_prime_sum_div_log_tendsto
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (C : ConjClasses (L ≃ₐ[K] L)) :
    Tendsto
      (fun s : ℝ => NumberField.Set.primeIdealZetaSum (NumberField.Chebotarev.frobeniusPrimeSet K L C) s /
        Real.log (1 / (s - 1)))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L))) := by
  have hd := NumberField.Set.hasDirichletDensity_of_hasNaturalDensity
    (NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet K L C)
  exact (NumberField.Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one
    (NumberField.Chebotarev.frobeniusPrimeSet K L C)
    ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L))).mp hd

/-- A closed one-sided weighted estimate on the genuine, already-unramified
Frobenius class. The weight is exactly norm to the power `-s` in
`primeIdealZetaSum`, with logarithmic normalization. -/
theorem class_weighted_lower_bound
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (C : ConjClasses (L ≃ₐ[K] L))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L) - ε) *
          Real.log (1 / (s - 1)) ≤
        NumberField.Set.primeIdealZetaSum (NumberField.Chebotarev.frobeniusPrimeSet K L C) s := by
  have hb := (tendsto_order.mp (class_prime_sum_div_log_tendsto K L C)).1
    (((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) - ε) (by linarith)
  have hlog := (Real.tendsto_log_one_div_sub_atTop (1 : ℝ)).eventually_gt_atTop 0
  filter_upwards [hb, hlog] with s hs hpos
  exact ((lt_div_iff₀ hpos).mp hs).le

/-- The same exact weighted estimate on an explicit interval to the right of
one, matching the interval shape used by the source quantitative boundary. -/
theorem class_weighted_lower_bound_interval
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (C : ConjClasses (L ≃ₐ[K] L))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L) - ε) *
          Real.log (1 / (s - 1)) ≤
        NumberField.Set.primeIdealZetaSum
          (NumberField.Chebotarev.frobeniusPrimeSet K L C) s := by
  obtain ⟨s₀, hs₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (class_weighted_lower_bound K L C ε hε)
  exact ⟨s₀, hs₀, fun s hs hs' => hsub ⟨hs, hs'⟩⟩

end C5ChebotarevBridge
