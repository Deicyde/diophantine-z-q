import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.RepeatedPrimeMixedTrace
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightRawSeriesBridge

/-!
# Identification of the weight-three series image in the repeated-prime mixed trace

For level `ℓ ≥ 3`:

* the weight-three class-series forms (values `∑_q eisSummand 3 (a + ℓ q₁, b + ℓ q₂)`) equal the
  unscaled all-weight class forms at weight `3` (`classSeriesForm_eq_raw`), so the class-series span
  equals the all-weight series span at weight `3` (`classSeriesSpan_eq_seriesSpanK`);
* the weight-three normalized trace equals the all-weight normalized trace at weight `3`
  (`normalizedTrace3_eq_traceK`);
* hence the trace of the upper class-series span lies in the lower class-series span
  (`trace_classSeries_mem`), and the target of the repeated-prime mixed trace lies in the lower
  class-series span plus the lower mixed span (`target_le`);
* both lie in the span of admissible degree-three torsion products (`target_le_degreeThree`).

Consequently, for `p ∈ {2, 3}`, `p ∣ ℓ`, `ℓ ≥ 3`, the actual normalized trace of every mixed form
`x_P λ_Q` at level `pℓ` (all integer labels) lies in the degree-three product span at level `ℓ`
(`trace_cross_mem_degreeThree_small_prime`). For general `p` the same follows from the slope
statement for every slope (`trace_cross_mem_degreeThree_of_slopes`), which is not proved here.
-/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.RepeatedPrimeMixedTraceBinder

open TorsionWeierstrassData TorsionWeightThree MixedWeightThreeAddition MixedWeightThreeDistribution
open DivisionEisensteinLevelMaps RepeatedPrimeMixedTrace AllWeightSeriesTrace

/-! ### The two series spans coincide at weight three -/

theorem classSeriesForm_eq_raw (N : ℕ) (h3 : 3 ≤ N) (a b : ℤ) :
    classSeriesForm N (by omega) a b = rawClassForm N h3 3 le_rfl ![a, b] := by
  apply DFunLike.ext
  intro τ
  rw [classSeriesForm_apply, rawClassForm_apply]
  rfl

theorem classSeriesSpan_eq_seriesSpanK (N : ℕ) (h3 : 3 ≤ N) :
    classSeriesSpan N (by omega) = seriesSpanK N h3 3 le_rfl := by
  rw [← rawClassForm_span_eq N h3 3 le_rfl]
  unfold classSeriesSpan
  congr 1
  ext f
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨![q.1, q.2], (classSeriesForm_eq_raw N h3 q.1 q.2).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(a 0, a 1), ?_⟩
    change classSeriesForm N _ (a 0) (a 1) = _
    rw [classSeriesForm_eq_raw N h3]
    congr 1
    ext i
    fin_cases i <;> rfl

/-! ### The two normalized traces coincide at weight three -/

theorem normalizedTrace3_eq_traceK (N M : ℕ) (hM : 0 < M) :
    normalizedTrace3 N M hM = normalizedTraceK N M 3 hM := by
  have : NeZero M := ⟨hM.ne'⟩
  apply LinearMap.ext
  intro f
  rw [normalizedTrace3_apply, normalizedTraceK_apply]

/-! ### Series image -/

theorem trace_classSeries_mem {ell M : ℕ} (h3 : 3 ≤ ell) (hM : 0 < M) (hlM : ell ∣ M)
    {f : Weight M 3} (hf : f ∈ classSeriesSpan M hM) :
    normalizedTrace3 ell M hM f ∈ classSeriesSpan ell (by omega) := by
  have h3M : 3 ≤ M := h3.trans (Nat.le_of_dvd hM hlM)
  rw [classSeriesSpan_eq_seriesSpanK M h3M] at hf
  rw [classSeriesSpan_eq_seriesSpanK ell h3, normalizedTrace3_eq_traceK]
  exact traceK_seriesSpan_all h3 hM hlM 3 le_rfl hf

theorem target_le (p ell : ℕ) (h3 : 3 ≤ ell) (hM : 0 < p * ell) :
    target p ell (by omega) hM ≤ lowerMixedSpan ell (by omega) ⊔ classSeriesSpan ell (by omega) := by
  apply sup_le le_sup_left
  rintro _ ⟨f, hf, rfl⟩
  exact Submodule.mem_sup_right (trace_classSeries_mem h3 hM (dvd_mul_left ell p) hf)

/-! ### Inclusion in the degree-three product span -/

theorem crossForm_mem_degreeThree (N : ℕ) (h3 : 3 ≤ N) (u v u' v' : ℤ) :
    crossForm N (by omega) u v u' v' ∈ degreeThreeProductSpan N (by omega) := by
  unfold crossForm
  apply lambdaTimesForm_mem_degreeThree
  rw [xForm_eq_quadratic_generator N (by omega) h3]
  exact TorsionQuadraticGenerators.xForm_mem_productSpan N h3 u v

theorem lowerMixedSpan_le (N : ℕ) (h3 : 3 ≤ N) :
    lowerMixedSpan N (by omega) ≤ degreeThreeProductSpan N (by omega) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl⟩
  exact crossForm_mem_degreeThree N h3 _ _ _ _

theorem classSeriesSpan_le (N : ℕ) (h3 : 3 ≤ N) :
    classSeriesSpan N (by omega) ≤ degreeThreeProductSpan N (by omega) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨q, rfl⟩
  exact Submodule.smul_mem _ _ (yForm_mem_degreeThree N (by omega) h3 q.1 q.2)

theorem target_le_degreeThree (p ell : ℕ) (h3 : 3 ≤ ell) (hM : 0 < p * ell) :
    target p ell (by omega) hM ≤ degreeThreeProductSpan ell (by omega) :=
  (target_le p ell h3 hM).trans (sup_le (lowerMixedSpan_le ell h3) (classSeriesSpan_le ell h3))

/-! ### Mixed trace endpoints -/

/-- **Repeated-prime mixed trace, `p ∈ {2, 3}`**: lower mixed forms plus lower class series. -/
theorem trace_cross_mem_lower_small_prime (p ell : ℕ) [Fact p.Prime] (h3 : 3 ≤ ell) (hpl : p ∣ ell)
    (hp : p = 2 ∨ p = 3) (a b c d : ℤ) :
    normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) a b c d) ∈
      lowerMixedSpan ell (by omega) ⊔ classSeriesSpan ell (by omega) :=
  target_le p ell h3 _ (trace_cross_mem_small_prime p ell (by omega) hpl hp a b c d)

/-- **Repeated-prime mixed trace, `p ∈ {2, 3}`**: in the degree-three product span. -/
theorem trace_cross_mem_degreeThree_small_prime (p ell : ℕ) [Fact p.Prime] (h3 : 3 ≤ ell)
    (hpl : p ∣ ell) (hp : p = 2 ∨ p = 3) (a b c d : ℤ) :
    normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) a b c d) ∈
      degreeThreeProductSpan ell (by omega) :=
  target_le_degreeThree p ell h3 _ (trace_cross_mem_small_prime p ell (by omega) hpl hp a b c d)

/-- General `p`, conditional on the slope statement for every slope (not proved here). -/
theorem trace_cross_mem_degreeThree_of_slopes (p ell : ℕ) [Fact p.Prime] (h3 : 3 ≤ ell)
    (hpl : p ∣ ell) (hS : ∀ σ : ℤ, SlopeClosed p ell (by omega) σ) (a b c d : ℤ) :
    normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) a b c d) ∈
      degreeThreeProductSpan ell (by omega) :=
  target_le_degreeThree p ell h3 _ (trace_cross_mem_of_slopes p ell (by omega) hpl hS a b c d)

end ZInQ.Contrib.HeckePrimeRationality.RepeatedPrimeMixedTraceBinder
