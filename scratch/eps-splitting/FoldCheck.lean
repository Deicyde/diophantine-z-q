import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.GrossZagierSplit

/-! eps-splitting manual fold check: `ZInQ.OneProof.frozenTarget` with the binder `hGZ` retyped from
`ZInQ.GZAlg.GrossZagierAlgOptCd` to the splitting leaf `ZInQ.GZSplit.GrossZagierCurveCdSplit`. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, from every statement still open.** -/
theorem _root_.ZInQ.EpsSplit.frozenTarget_split
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZSplit.GrossZagierCurveCdSplit) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open55 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX (ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only h21C) (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C h21C) ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg (ZInQ.GZSplit.grossZagierAlgOptCd_of_split hGZ) ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.EpsSplit.frozenTarget_split
#print axioms ZInQ.GZSplit.grossZagierAlgOptCd_of_split
#print axioms ZInQ.GZSplit.grossZagierCurveCdSplit_of_curveCd
#print axioms ZInQ.EpsSplit.splitType_epsD
#print axioms ZInQ.EpsSplit.quadChar_eq_epsD
#print axioms ZInQ.EpsSplit.adjoin_thetaO_eq_top
