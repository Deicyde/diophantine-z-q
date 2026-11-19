import ZInQKernel.Contrib.OneProof.ForwardRankLiterature

/-!
# Closed public checks for the forward-rank literature adapter

These checks retain `ForwardRankAtMostOne` as an explicit input. They do not
certify the cited literature in Lean or remove a hypothesis from the main theorem.
-/

set_option autoImplicit false
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.maxSteps 1000000

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Manuscript.ForwardRankLiterature

#check @ZInQ.Manuscript.ForwardRankLiterature.analyticRankAt_one_iff
example : ∀ E : WeierstrassCurve ℚ,
    AnalyticRankAt E 1 ↔ AnalyticRankOne E :=
  @ZInQ.Manuscript.ForwardRankLiterature.analyticRankAt_one_iff
#print axioms ZInQ.Manuscript.ForwardRankLiterature.analyticRankAt_one_iff

#check @ZInQ.Manuscript.ForwardRankLiterature.ForwardRankAtMostOne
example : ForwardRankAtMostOne ↔
    ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ r : ℕ, r ≤ 1 →
      AnalyticRankAt E r → Module.rank ℤ E.toAffine.Point = r ∧ Finite (sha E) :=
  Iff.rfl
#print axioms ZInQ.Manuscript.ForwardRankLiterature.ForwardRankAtMostOne

#check @ZInQ.Manuscript.ForwardRankLiterature.kolyvaginThm1_of_forwardRankAtMostOne
example : ForwardRankAtMostOne → PoleS12.KolyvaginThm1 :=
  @ZInQ.Manuscript.ForwardRankLiterature.kolyvaginThm1_of_forwardRankAtMostOne
#print axioms ZInQ.Manuscript.ForwardRankLiterature.kolyvaginThm1_of_forwardRankAtMostOne

#check @ZInQ.Manuscript.ForwardRankLiterature.rankOne_and_finiteSha
example : ∀ (_ : ForwardRankAtMostOne) (E : WeierstrassCurve ℚ),
    E.IsElliptic → AnalyticRankOne E →
      Module.rank ℤ E.toAffine.Point = 1 ∧ Finite (sha E) :=
  @ZInQ.Manuscript.ForwardRankLiterature.rankOne_and_finiteSha
#print axioms ZInQ.Manuscript.ForwardRankLiterature.rankOne_and_finiteSha

#check @ZInQ.Manuscript.ForwardRankLiterature.rankZero_and_finiteSha
example : ∀ (_ : ForwardRankAtMostOne) (E : WeierstrassCurve ℚ),
    E.IsElliptic → AnalyticRankAt E 0 →
      Module.rank ℤ E.toAffine.Point = 0 ∧ Finite (sha E) :=
  @ZInQ.Manuscript.ForwardRankLiterature.rankZero_and_finiteSha
#print axioms ZInQ.Manuscript.ForwardRankLiterature.rankZero_and_finiteSha
