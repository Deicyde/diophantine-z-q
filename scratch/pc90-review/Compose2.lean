import ZInQKernel.OneProof.Main

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

/-- frozenTarget with Kolyvagin's Theorem 1 in the printed `r ≤ 1` form (kolyv-cst-printed); `hKum` kept
(the proof `PoleS12.kummerSelmerM` cannot be imported next to the H chain: divisorSum clash). -/
theorem frozenTarget_printed
    (r : HDec.HSyn.OpenResearchLeaves57) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves27)
    (hRC : SelmerTwoPower.RestrictedConverseGenuine) (h54 : PoleS12.Lemma54)
    (hKum : PoleS12.KummerSelmerM)
    (hB : PoleS12.BCDTThmA) (hK : KolyvaginThm1Printed) : ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l hRC h54 hKum hB (kolyvaginThm1_of_printed hK)

end ZInQ.PC90Review

#print axioms ZInQ.PC90Review.frozenTarget_printed
#print axioms ZInQ.OneProof.frozenTarget
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
#print axioms ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_mw
