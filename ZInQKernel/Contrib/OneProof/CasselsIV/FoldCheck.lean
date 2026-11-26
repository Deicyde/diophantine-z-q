import ZInQKernel.OneProof.H.TailZ106
import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal
import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.OneProof.SilvermanRankOne
import ZInQKernel.Contrib.OneProof.CasselsIV.Glue

/-!
# Fold check: the frozen target with `hCT` restated to Cassels (1962), Theorem 1.1

The imports are those of `ZInQKernel/OneProof/Main.lean`, plus `CasselsIV.Glue`; this file does not
import `ZInQKernel.OneProof.Main`.

`frozenTarget_with_casselsIV` has the hypotheses of `ZInQ.OneProof.frozenTarget`, except that
`hCT` is `ZInQ.Manuscript.SelmerTwoPower.CasselsIVThm11Elliptic` (Cassels, J. reine angew. Math.
211 (1962), Theorem 1.1, p. 95, with §3 (viii), p. 104, at `k = ℚ`). Its body is the body of
`ZInQ.OneProof.frozenTarget` at the base of this file, with the consumer
`poleCompleteness_of_rankOne` replaced by `poleCompleteness_of_rankOne_PS` and the row fed through
`casselsTatePairingCurvesPS_of_casselsIV`. The number of hypotheses is the same.

This is additive evidence only: nothing here folds the swap into `Main.lean`.
-/

namespace ZInQ.OneProof

/-- **Theorem 1.1 of the manuscript with `hCT` restated to Cassels (1962), Theorem 1.1.** The body
of `ZInQ.OneProof.frozenTarget`, with `poleCompleteness_of_rankOne_PS` as the consumer and the
glue `casselsTatePairingCurvesPS_of_casselsIV` in front of it. -/
theorem CasselsIV.frozenTarget_with_casselsIV
    (r : HDec.HSyn.OpenResearchLeaves78) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves30)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.SelmerTwoPower.CasselsIVThm11Elliptic)
    (hRank : ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open99 r t l)
    (ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne_PS hRC
      (ZInQ.Manuscript.PoleS12.casselsTatePairingCurvesPS_of_casselsIV hCT)
      (ZInQ.Manuscript.PoleS12.SilvermanRank.rankOne_of_aec hRank))

end ZInQ.OneProof

#print axioms ZInQ.OneProof.CasselsIV.frozenTarget_with_casselsIV
#print axioms ZInQ.Manuscript.SelmerTwoPower.CasselsIVThm11
#print axioms ZInQ.Manuscript.SelmerTwoPower.CasselsIVThm11Elliptic
#print axioms ZInQ.Manuscript.SelmerTwoPower.casselsTatePairingPS_of_casselsIV
#print axioms ZInQ.Manuscript.PoleS12.casselsTatePairingCurvesPS_of_casselsIV
#print axioms ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne_casselsIV
