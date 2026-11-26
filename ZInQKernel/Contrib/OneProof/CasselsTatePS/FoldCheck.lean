import ZInQKernel.OneProof.H.TailZ105
import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal
import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.OneProof.SilvermanRankOne
import ZInQKernel.Contrib.OneProof.CasselsTatePS.Basic

/-!
# Fold check: the frozen target with `hCT` in the form printed by Poonen–Stoll

The imports are those of `ZInQKernel/OneProof/Main.lean`, plus `CasselsTatePS.Basic`; this file
does not import `ZInQKernel.OneProof.Main`.

`frozenTarget_with_hCTps` has the hypotheses of `ZInQ.OneProof.frozenTarget`, except that `hCT` is
`ZInQ.Manuscript.PoleS12.CasselsTatePairingCurvesPS` (Poonen–Stoll, Ann. of Math. 150 (1999),
Theorem 8 (1) ⇒ (2), pp. 1122–1123, with Corollary 12 at `g = 1`, p. 1126). Its body is the body
of `ZInQ.OneProof.frozenTarget` at the base of this file, with the consumer
`poleCompleteness_of_rankOne` replaced by `poleCompleteness_of_rankOne_PS`.

`frozenTarget_of_current_via_PS` recovers the current hypothesis list through
`casselsTatePairingCurvesPS_of_current`, so the swap loses nothing and keeps the count.

This is additive evidence only: nothing here folds the swap into `Main.lean`.
-/

namespace ZInQ.OneProof

/-- **Theorem 1.1 with `hCT` in the printed form of Poonen–Stoll.** The body of
`ZInQ.OneProof.frozenTarget`, verbatim, with `poleCompleteness_of_rankOne_PS` as the consumer. -/
theorem CasselsTatePS.frozenTarget_with_hCTps
    (r : HDec.HSyn.OpenResearchLeaves78) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves29)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurvesPS)
    (hRank : ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open98 r t l)
    (ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne_PS hRC hCT
      (ZInQ.Manuscript.PoleS12.SilvermanRank.rankOne_of_aec hRank))

/-- **The current hypothesis list still gives the frozen target through the printed form.** -/
theorem CasselsTatePS.frozenTarget_of_current_via_PS
    (r : HDec.HSyn.OpenResearchLeaves78) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves29)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves)
    (hRank : ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne) :
    ZInQ.FrozenTarget :=
  CasselsTatePS.frozenTarget_with_hCTps r t l hRC
    (ZInQ.Manuscript.PoleS12.casselsTatePairingCurvesPS_of_current hCT) hRank

end ZInQ.OneProof

#print axioms ZInQ.OneProof.CasselsTatePS.frozenTarget_with_hCTps
#print axioms ZInQ.OneProof.CasselsTatePS.frozenTarget_of_current_via_PS
#print axioms ZInQ.Manuscript.PoleS12.CasselsTatePairingCurvesPS
#print axioms ZInQ.Manuscript.PoleS12.casselsTatePairingCurvesPS_of_current
#print axioms ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne_PS
