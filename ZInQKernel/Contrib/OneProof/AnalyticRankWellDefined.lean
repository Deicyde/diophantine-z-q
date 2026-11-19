import ZInQKernel.Contrib.OneProof.ForwardRankLiterature
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order

/-!
# The analytic-rank predicates have a unique continuation and order

The entire continuation in the existing analytic-rank predicates is determined
by its values on `Re(s) > 3/2`. The identity theorem therefore makes its order
at `s = 1` independent of the chosen witness. For an actual entire continuation,
rank zero means a nonzero central value, and rank one means a simple zero.

These are proofs from the analytic identity theorem and vanishing-order APIs,
not assumptions about modularity, Kolyvagin, Selmer groups, or rational points.
They use the existing `E.LSeries`, `AnalyticRankAt` and `AnalyticRankOne` without
changing those definitions. They do not prove that a continuation exists for
every curve or that the restricted converse holds.
-/

set_option autoImplicit false

namespace ZInQ.Manuscript.ForwardRankLiterature

open scoped Topology

/-- Two entire continuations of the same L-series on the defining half-plane
are equal as functions, not merely at the central point. -/
theorem continuations_unique (E : WeierstrassCurve ℚ) (F G : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hFE : ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s)
    (hGE : ∀ s : ℂ, 3 / 2 < s.re → G s = E.LSeries s) : F = G := by
  have hopen : IsOpen {s : ℂ | (3 / 2 : ℝ) < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have htwo : (2 : ℂ) ∈ {s : ℂ | (3 / 2 : ℝ) < s.re} := by norm_num
  have heq : F =ᶠ[𝓝 (2 : ℂ)] G := by
    filter_upwards [hopen.mem_nhds htwo] with s hs
    exact (hFE s hs).trans (hGE s hs).symm
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun s _ => hF.analyticAt s
  have hGa : AnalyticOnNhd ℂ G Set.univ := fun s _ => hG.analyticAt s
  exact hFa.eq_of_eventuallyEq hGa heq

/-- The natural-number analytic rank of a curve is unique whenever it exists. -/
theorem analyticRankAt_unique (E : WeierstrassCurve ℚ) (r t : ℕ)
    (hr : AnalyticRankAt E r) (ht : AnalyticRankAt E t) : r = t := by
  obtain ⟨F, hF, hFE, hFr⟩ := hr
  obtain ⟨G, hG, hGE, hGt⟩ := ht
  have hFG := continuations_unique E F G hF hG hFE hGE
  have hcast : (r : ℕ∞) = (t : ℕ∞) := by
    rw [← hFr, hFG, hGt]
  exact (Nat.cast_inj (R := ℕ∞)).mp hcast

/-- Every actual entire continuation computes the same order used in the
existential analytic-rank predicate. -/
theorem analyticRankAt_iff_order (E : WeierstrassCurve ℚ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F)
    (hFE : ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) (r : ℕ) :
    AnalyticRankAt E r ↔ analyticOrderAt F 1 = r := by
  constructor
  · rintro ⟨G, hG, hGE, hGr⟩
    have hGF := continuations_unique E G F hG hF hGE hFE
    simpa only [hGF] using hGr
  · intro hFr
    exact ⟨F, hF, hFE, hFr⟩

/-- The manuscript's rank-one predicate has the same witness-independent
central order as the general analytic-rank predicate. -/
theorem analyticRankOne_iff_order (E : WeierstrassCurve ℚ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F)
    (hFE : ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) :
    AnalyticRankOne E ↔ analyticOrderAt F 1 = 1 := by
  rw [← analyticRankAt_one_iff E]
  simpa only [Nat.cast_one] using analyticRankAt_iff_order E F hF hFE 1

/-- Rank zero of an actual entire continuation is nonvanishing at `s = 1`.
Differentiability rules out the nonanalytic junk-value branch of analytic order. -/
theorem analyticRankAt_zero_iff_nonzero (E : WeierstrassCurve ℚ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F)
    (hFE : ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) :
    AnalyticRankAt E 0 ↔ F 1 ≠ 0 := by
  rw [analyticRankAt_iff_order E F hF hFE 0, Nat.cast_zero]
  exact (hF.analyticAt 1).analyticOrderAt_eq_zero

/-- Rank one means exactly that the central value vanishes and its derivative
does not. This checks the conventional simple-zero interpretation. -/
theorem analyticRankOne_iff_simple_zero (E : WeierstrassCurve ℚ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F)
    (hFE : ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) :
    AnalyticRankOne E ↔ F 1 = 0 ∧ deriv F 1 ≠ 0 := by
  rw [analyticRankOne_iff_order E F hF hFE]
  constructor
  · intro horder
    have hzero : F 1 = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero (by
      rw [horder]
      exact one_ne_zero)
    have hderivOrder : analyticOrderAt (deriv F) 1 = 0 := by
      have h := (analyticOrderAt_deriv_eq_iff (hF.analyticAt 1) hzero (n := 0)).mp
        (by simpa only [Nat.cast_zero, zero_add] using horder)
      simpa only [Nat.cast_zero] using h
    exact ⟨hzero, ((hF.analyticAt 1).deriv.analyticOrderAt_eq_zero).mp hderivOrder⟩
  · rintro ⟨hzero, hderiv⟩
    exact (hF.analyticAt 1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv

/-- An analytic-rank witness supplies exactly one entire continuation with the
required half-plane values; existence is not asserted without that witness. -/
theorem existsUnique_continuation_of_analyticRankAt (E : WeierstrassCurve ℚ) (r : ℕ)
    (hr : AnalyticRankAt E r) :
    ∃! F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) := by
  obtain ⟨F, hF, hFE, _⟩ := hr
  refine ⟨F, ⟨hF, hFE⟩, ?_⟩
  intro G hG
  exact continuations_unique E G F hG.1 hF hG.2 hFE

end ZInQ.Manuscript.ForwardRankLiterature
