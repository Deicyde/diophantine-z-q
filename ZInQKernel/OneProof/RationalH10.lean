import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.H10Reduction

/-!
# Rational H10 from the single theorem

Composes `ZInQ.OneProof.frozenTarget` with the consumer of upstream PR #150
(`ZInQ.Contrib.H10Reduction.rational_not_computable_of_frozenTarget`): no algorithm decides
rational solvability of integer polynomials, assuming the statements `frozenTarget` still takes
as hypotheses and the undecidability of integer solvability for that file's coding of polynomials
(`hZ`, the integer H10 premise; no DPRM theorem is formalized here).
-/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Rational H10, conditional:** from `frozenTarget`'s open statements and integer H10 for
`H10Reduction`'s coding. -/
theorem _root_.ZInQ.OneProof.rationalH10
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd)
    (hZ : ¬ ComputablePred ZInQ.Contrib.H10Reduction.IntCodeSolvable) :
    ¬ ComputablePred ZInQ.Contrib.H10Reduction.RatCodeSolvable :=
  ZInQ.Contrib.H10Reduction.rational_not_computable_of_frozenTarget
    (ZInQ.OneProof.frozenTarget r t l h21C hCM h33 hBFH hGZ) hZ

end ZInQ.Contrib.TYZChain
