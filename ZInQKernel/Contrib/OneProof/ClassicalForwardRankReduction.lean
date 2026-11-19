import ZInQKernel.Contrib.OneProof.AnalyticRankWellDefined

/-!
# A classical formulation connected to the existing Kolyvagin input

The standard forward theorem for elliptic curves over `ℚ` says that a nonzero
central value gives rank zero and finite `Sha`, while a simple central zero
gives rank one and finite `Sha`. It is the consequence of BCDT Theorem A,
Silverman, second edition, C.13.6 p. 442, and Kolyvagin, ICM Kyoto 1990,
Theorem 1 p. 430, already cited in `ForwardRankLiterature`.

`ClassicalCentralValueRank` states this consequence on the same actual entire
continuations, rational point groups and all-place `Sha` as the existing
analytic-rank predicates. It is an explicit proposition, not evidence for it.
The verified analytic dictionary proves that this formulation is equivalent
to `ForwardRankAtMostOne`, rather than a stronger replacement assumption.

The final reduction targets the existing `PoleS12.KolyvaginThm1` hypothesis.
It is conditional on the named classical result: no open arithmetic premise
is counted as discharged merely because the reduction compiles. Neither
`Main`, the legacy hypothesis, nor the restricted converse is changed.
-/

set_option autoImplicit false

namespace ZInQ.Manuscript.ForwardRankLiterature

open SelmerTwoPower (sha)

/-- The conventional central-value/simple-zero form of the classical low-rank
forward theorem. It is a consequence of universal modularity and Kolyvagin,
not a literal transcription with modularity silently omitted. The function
`F` is an actual entire continuation of the unchanged `E.LSeries`; the raw
Dirichlet series at the central point is not substituted for its continuation. -/
def ClassicalCentralValueRank : Prop :=
  ∀ (E : WeierstrassCurve ℚ), E.IsElliptic → ∀ F : ℂ → ℂ,
    Differentiable ℂ F →
    (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) →
      (F 1 ≠ 0 → Module.rank ℤ E.toAffine.Point = 0 ∧ Finite (sha E)) ∧
      (F 1 = 0 → deriv F 1 ≠ 0 →
        Module.rank ℤ E.toAffine.Point = 1 ∧ Finite (sha E))

/-- The proved analytic dictionary translates the forward theorem to its
central-value and simple-zero formulation. -/
theorem classicalCentralValueRank_of_forwardRank (h : ForwardRankAtMostOne) :
    ClassicalCentralValueRank := by
  intro E hE F hF hFE
  constructor
  · intro hvalue
    exact rankZero_and_finiteSha h E hE
      ((analyticRankAt_zero_iff_nonzero E F hF hFE).mpr hvalue)
  · intro hvalue hderiv
    exact rankOne_and_finiteSha h E hE
      ((analyticRankOne_iff_simple_zero E F hF hFE).mpr ⟨hvalue, hderiv⟩)

/-- Conversely, the same dictionary recovers all natural analytic ranks at
most one. No new existence or arithmetic hypothesis is introduced. -/
theorem forwardRank_of_classicalCentralValueRank (h : ClassicalCentralValueRank) :
    ForwardRankAtMostOne := by
  intro E hE r hbound hr
  obtain ⟨F, hF, hFE, horder⟩ := hr
  have hcases : r = 0 ∨ r = 1 := by omega
  rcases hcases with rfl | rfl
  · have hzero : AnalyticRankAt E 0 := ⟨F, hF, hFE, horder⟩
    have hvalue := (analyticRankAt_zero_iff_nonzero E F hF hFE).mp hzero
    simpa only [Nat.cast_zero] using (h E hE F hF hFE).1 hvalue
  · have hone : AnalyticRankOne E :=
      (analyticRankAt_one_iff E).mp ⟨F, hF, hFE, horder⟩
    obtain ⟨hvalue, hderiv⟩ := (analyticRankOne_iff_simple_zero E F hF hFE).mp hone
    simpa only [Nat.cast_one] using (h E hE F hF hFE).2 hvalue hderiv

/-- The classical central-value statement is exactly equivalent to the
existing forward literature input, not an additional arithmetic requirement. -/
theorem forwardRank_iff_classicalCentralValueRank :
    ForwardRankAtMostOne ↔ ClassicalCentralValueRank :=
  ⟨classicalCentralValueRank_of_forwardRank, forwardRank_of_classicalCentralValueRank⟩

/-- Direct connection to the existing `hK` statement. The remaining input is
the explicitly cited classical forward result, not the manuscript's converse. -/
theorem kolyvaginThm1_of_classicalCentralValueRank (h : ClassicalCentralValueRank) :
    PoleS12.KolyvaginThm1 :=
  kolyvaginThm1_of_forwardRankAtMostOne (forwardRank_of_classicalCentralValueRank h)

end ZInQ.Manuscript.ForwardRankLiterature
