import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.Gamma0QExpansion

/-! gamma0-qexp: the manual fold of `ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`)
without the frozenTarget binder `hQ : ZInQ.GZAlg.Gamma0QExpansion`, filled by
`ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof`. The body is Main's, with `hQ` replaced. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, from every statement still open, without `hQ`.** -/
theorem _root_.ZInQ.OneProof.frozenTarget_noQ
    (r : HDec.HSyn.OpenResearchLeaves29) (t : HDec.HSyn.OpenTextbookLeaves15) (l : HDec.HSyn.OpenAddedLeaves20)
    (h11 : TYZThm11Integral)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) (hW : ZInQ.CdOpt.EtaW32Character) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open41 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof hfx hL29 ZInQ.Contrib.T21Proof.tyzThm21At31 hP23) hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed hCM
      (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof hW)
      ZInQ.GZConj.grossConjugationCd)

/-- Sanity: the folded theorem is Main's theorem with `hQ` filled. -/
example (r : HDec.HSyn.OpenResearchLeaves29) (t : HDec.HSyn.OpenTextbookLeaves15) (l : HDec.HSyn.OpenAddedLeaves20)
    (h11 : TYZThm11Integral)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) (hW : ZInQ.CdOpt.EtaW32Character) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l h11 hfx hL29 hP23 hCM h33 hBFH hGZ
    ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof hW

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.OneProof.frozenTarget_noQ
