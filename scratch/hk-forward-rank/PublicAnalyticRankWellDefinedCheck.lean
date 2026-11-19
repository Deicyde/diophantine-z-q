import ZInQKernel.Contrib.OneProof.AnalyticRankWellDefined

/-!
# Public consumers of analytic-continuation uniqueness

All types use the existing L-series and analytic-rank predicates. No forward
rank theorem or other unproved arithmetic proposition is supplied to these checks.
-/

set_option autoImplicit false
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.maxSteps 1000000

open ZInQ.Manuscript ZInQ.Manuscript.ForwardRankLiterature

#check @ZInQ.Manuscript.ForwardRankLiterature.continuations_unique
example : ∀ (E : WeierstrassCurve ℚ) (F G : ℂ → ℂ),
    Differentiable ℂ F → Differentiable ℂ G →
    (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) →
    (∀ s : ℂ, 3 / 2 < s.re → G s = E.LSeries s) → F = G :=
  @ZInQ.Manuscript.ForwardRankLiterature.continuations_unique
#print axioms ZInQ.Manuscript.ForwardRankLiterature.continuations_unique

#check @ZInQ.Manuscript.ForwardRankLiterature.analyticRankAt_unique
example : ∀ (E : WeierstrassCurve ℚ) (r t : ℕ),
    AnalyticRankAt E r → AnalyticRankAt E t → r = t :=
  @ZInQ.Manuscript.ForwardRankLiterature.analyticRankAt_unique
#print axioms ZInQ.Manuscript.ForwardRankLiterature.analyticRankAt_unique

#check @ZInQ.Manuscript.ForwardRankLiterature.analyticRankAt_iff_order
example : ∀ (E : WeierstrassCurve ℚ) (F : ℂ → ℂ),
    Differentiable ℂ F →
    (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) → ∀ r : ℕ,
      AnalyticRankAt E r ↔ analyticOrderAt F 1 = r :=
  @ZInQ.Manuscript.ForwardRankLiterature.analyticRankAt_iff_order
#print axioms ZInQ.Manuscript.ForwardRankLiterature.analyticRankAt_iff_order

#check @ZInQ.Manuscript.ForwardRankLiterature.analyticRankOne_iff_order
example : ∀ (E : WeierstrassCurve ℚ) (F : ℂ → ℂ),
    Differentiable ℂ F →
    (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) →
      (AnalyticRankOne E ↔ analyticOrderAt F 1 = 1) :=
  @ZInQ.Manuscript.ForwardRankLiterature.analyticRankOne_iff_order
#print axioms ZInQ.Manuscript.ForwardRankLiterature.analyticRankOne_iff_order

#check @ZInQ.Manuscript.ForwardRankLiterature.analyticRankAt_zero_iff_nonzero
example : ∀ (E : WeierstrassCurve ℚ) (F : ℂ → ℂ),
    Differentiable ℂ F →
    (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) →
      (AnalyticRankAt E 0 ↔ F 1 ≠ 0) :=
  @ZInQ.Manuscript.ForwardRankLiterature.analyticRankAt_zero_iff_nonzero
#print axioms ZInQ.Manuscript.ForwardRankLiterature.analyticRankAt_zero_iff_nonzero

#check @ZInQ.Manuscript.ForwardRankLiterature.analyticRankOne_iff_simple_zero
example : ∀ (E : WeierstrassCurve ℚ) (F : ℂ → ℂ),
    Differentiable ℂ F →
    (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) →
      (AnalyticRankOne E ↔ F 1 = 0 ∧ deriv F 1 ≠ 0) :=
  @ZInQ.Manuscript.ForwardRankLiterature.analyticRankOne_iff_simple_zero
#print axioms ZInQ.Manuscript.ForwardRankLiterature.analyticRankOne_iff_simple_zero

#check @ZInQ.Manuscript.ForwardRankLiterature.existsUnique_continuation_of_analyticRankAt
example : ∀ (E : WeierstrassCurve ℚ) (r : ℕ), AnalyticRankAt E r →
    ∃! F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) :=
  @ZInQ.Manuscript.ForwardRankLiterature.existsUnique_continuation_of_analyticRankAt
#print axioms ZInQ.Manuscript.ForwardRankLiterature.existsUnique_continuation_of_analyticRankAt

example (E : WeierstrassCurve ℚ) (r t : ℕ) (hne : r ≠ t) :
    ¬ (AnalyticRankAt E r ∧ AnalyticRankAt E t) := by
  rintro ⟨hr, ht⟩
  exact hne (analyticRankAt_unique E r t hr ht)

example (E : WeierstrassCurve ℚ) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hFE : ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) (hA : AnalyticRankOne E) :
    F 1 = 0 := ((analyticRankOne_iff_simple_zero E F hF hFE).mp hA).1

example (E : WeierstrassCurve ℚ) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hFE : ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) (hA : AnalyticRankOne E) :
    deriv F 1 ≠ 0 := ((analyticRankOne_iff_simple_zero E F hF hFE).mp hA).2

example (E : WeierstrassCurve ℚ) (hA : AnalyticRankOne E) :
    ∃! F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) :=
  existsUnique_continuation_of_analyticRankAt E 1 ((analyticRankAt_one_iff E).mpr hA)
