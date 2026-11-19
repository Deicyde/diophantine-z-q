import ZInQKernel.Contrib.OneProof.ClassicalForwardRankReduction

/-!
# Public checks of the existing-assumption connection

The reductions keep the classical theorem as an input. The equivalence ensures
that its conventional central-value form is not a stronger replacement premise.
-/

set_option autoImplicit false
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.maxSteps 1000000

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Manuscript.ForwardRankLiterature

#check @ZInQ.Manuscript.ForwardRankLiterature.ClassicalCentralValueRank
example : ClassicalCentralValueRank ↔
    (∀ (E : WeierstrassCurve ℚ), E.IsElliptic → ∀ F : ℂ → ℂ,
      Differentiable ℂ F →
      (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) →
        (F 1 ≠ 0 → Module.rank ℤ E.toAffine.Point = 0 ∧ Finite (sha E)) ∧
        (F 1 = 0 → deriv F 1 ≠ 0 →
          Module.rank ℤ E.toAffine.Point = 1 ∧ Finite (sha E))) := Iff.rfl
#print axioms ZInQ.Manuscript.ForwardRankLiterature.ClassicalCentralValueRank
#print ZInQ.Manuscript.ForwardRankLiterature.ClassicalCentralValueRank

#check @ZInQ.Manuscript.ForwardRankLiterature.classicalCentralValueRank_of_forwardRank
example : ForwardRankAtMostOne → ClassicalCentralValueRank :=
  @ZInQ.Manuscript.ForwardRankLiterature.classicalCentralValueRank_of_forwardRank
#print axioms ZInQ.Manuscript.ForwardRankLiterature.classicalCentralValueRank_of_forwardRank

#check @ZInQ.Manuscript.ForwardRankLiterature.forwardRank_of_classicalCentralValueRank
example : ClassicalCentralValueRank → ForwardRankAtMostOne :=
  @ZInQ.Manuscript.ForwardRankLiterature.forwardRank_of_classicalCentralValueRank
#print axioms ZInQ.Manuscript.ForwardRankLiterature.forwardRank_of_classicalCentralValueRank

#check @ZInQ.Manuscript.ForwardRankLiterature.forwardRank_iff_classicalCentralValueRank
example : ForwardRankAtMostOne ↔ ClassicalCentralValueRank :=
  @ZInQ.Manuscript.ForwardRankLiterature.forwardRank_iff_classicalCentralValueRank
#print axioms ZInQ.Manuscript.ForwardRankLiterature.forwardRank_iff_classicalCentralValueRank

#check @ZInQ.Manuscript.ForwardRankLiterature.kolyvaginThm1_of_classicalCentralValueRank
example : ClassicalCentralValueRank → PoleS12.KolyvaginThm1 :=
  @ZInQ.Manuscript.ForwardRankLiterature.kolyvaginThm1_of_classicalCentralValueRank
#print axioms ZInQ.Manuscript.ForwardRankLiterature.kolyvaginThm1_of_classicalCentralValueRank

example (h : ClassicalCentralValueRank) (E : WeierstrassCurve ℚ) (hE : E.IsElliptic)
    (hM : PoleS12.IsModular E) (hA : AnalyticRankOne E) :
    Module.rank ℤ E.toAffine.Point = 1 ∧ Finite (sha E) :=
  kolyvaginThm1_of_classicalCentralValueRank h E hE hM hA

example (h : ForwardRankAtMostOne) : ClassicalCentralValueRank :=
  forwardRank_iff_classicalCentralValueRank.mp h

example (h : ClassicalCentralValueRank) : ForwardRankAtMostOne :=
  forwardRank_iff_classicalCentralValueRank.mpr h
