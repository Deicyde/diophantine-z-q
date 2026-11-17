import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal

/-! pc90-review (6): does the proved Kummer identification combine with the H chain's import closure?
If the Tau Ceti / AnthropicFLT `divisorSum` clash is real, this file fails at the imports. -/

namespace ZInQ.PC90Review

open ZInQ.Manuscript

/-- Copied from origin/wip/kolyv-cst-printed c12a1a03d (KolyvCST/Kolyvagin.lean). -/
def AnalyticRank (E : WeierstrassCurve ℚ) (r : ℕ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) ∧
    analyticOrderAt F 1 = r

theorem analyticRank_one_iff (E : WeierstrassCurve ℚ) :
    AnalyticRank E 1 ↔ AnalyticRankOne E := by
  simp only [AnalyticRank, AnalyticRankOne, Nat.cast_one]

def KolyvaginThm1Printed : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → PoleS12.IsModular E → ∀ r : ℕ, r ≤ 1 →
    AnalyticRank E r → Module.rank ℤ E.toAffine.Point = r ∧ Finite (SelmerTwoPower.sha E)

theorem kolyvaginThm1_of_printed (h : KolyvaginThm1Printed) : PoleS12.KolyvaginThm1 := by
  intro E hE hM hA
  have := h E hE hM 1 le_rfl ((analyticRank_one_iff E).mpr hA)
  simpa using this

/-- frozenTarget without `hKum` (the Kummer identification proved by `PoleS12.kummerSelmerM`). -/
theorem frozenTarget_noKum
    (r : HDec.HSyn.OpenResearchLeaves57) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves27)
    (hRC : SelmerTwoPower.RestrictedConverseGenuine) (h54 : PoleS12.Lemma54)
    (hB : PoleS12.BCDTThmA) (hK : PoleS12.KolyvaginThm1) : ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l hRC h54 PoleS12.kummerSelmerM hB hK

/-- The same with Kolyvagin's Theorem 1 in the printed `r ≤ 1` form. -/
theorem frozenTarget_noKum_printed
    (r : HDec.HSyn.OpenResearchLeaves57) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves27)
    (hRC : SelmerTwoPower.RestrictedConverseGenuine) (h54 : PoleS12.Lemma54)
    (hB : PoleS12.BCDTThmA) (hK : KolyvaginThm1Printed) : ZInQ.FrozenTarget :=
  frozenTarget_noKum r t l hRC h54 hB (kolyvaginThm1_of_printed hK)

end ZInQ.PC90Review

#print axioms ZInQ.PC90Review.frozenTarget_noKum
#print axioms ZInQ.PC90Review.frozenTarget_noKum_printed
