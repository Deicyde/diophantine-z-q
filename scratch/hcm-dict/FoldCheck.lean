import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.ShimuraMainCM

/-! hcm-dict: the manual fold of `hCM` (a top-level argument of `frozenTarget`, so autofold does not apply).

`frozenTarget_hCMPrinted` is `frozenTarget` with `hCM : T5Glue.ShimuraMainCM` replaced by the printed leaf
`hCM : ZInQ.Contrib.HCMDict.ShimuraThm54`. `frozenTarget_hCMPrinted'` is the folded `Main.lean` body itself: the text
of `ZInQ.OneProof.frozenTarget` with the binder's type changed and both uses of `hCM` replaced by
`(ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM)`; the folded `Main.lean` adds
`import ZInQKernel.Contrib.OneProof.ShimuraMainCM`. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_hCMPrinted
    (r : HDec.HSyn.OpenResearchLeaves29) (t : HDec.HSyn.OpenTextbookLeaves15) (l : HDec.HSyn.OpenAddedLeaves20)
    (h11 : TYZThm11Integral)
    (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l h11 hL29 (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33 hBFH hGZ

theorem frozenTarget_hCMPrinted'
    (r : HDec.HSyn.OpenResearchLeaves29) (t : HDec.HSyn.OpenTextbookLeaves15) (l : HDec.HSyn.OpenAddedLeaves20)
    (h11 : TYZThm11Integral)
    (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open41 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists hL29 ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM)
      (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_hCMPrinted
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_hCMPrinted'
