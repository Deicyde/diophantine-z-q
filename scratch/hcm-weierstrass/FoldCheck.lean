import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.ShimuraThm54Biholo

/-! hcm-weierstrass: the manual fold of `hCM` (a top-level argument of `frozenTarget`, so autofold does not apply).

`frozenTarget_hCMBiholo` is `frozenTarget` with `hCM : ZInQ.Contrib.HCMDict.ShimuraThm54` replaced by the leaf
`hCM : ZInQ.Contrib.HCMWeierstrass.ShimuraThm54Biholo`. `frozenTarget_hCMBiholo'` is the folded `Main.lean` body
itself: the text of `ZInQ.OneProof.frozenTarget` with the binder's type changed and every use of `hCM` replaced by
`(ZInQ.Contrib.HCMWeierstrass.shimuraThm54_of_biholo hCM)`; the folded `Main.lean` adds
`import ZInQKernel.Contrib.OneProof.ShimuraThm54Biholo`. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_hCMBiholo
    (r : HDec.HSyn.OpenResearchLeaves40) (t : HDec.HSyn.OpenTextbookLeaves17) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMWeierstrass.ShimuraThm54Biholo)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l h21C (ZInQ.Contrib.HCMWeierstrass.shimuraThm54_of_biholo hCM) h33 hBFH hGZ

theorem frozenTarget_hCMBiholo'
    (r : HDec.HSyn.OpenResearchLeaves40) (t : HDec.HSyn.OpenTextbookLeaves17) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMWeierstrass.ShimuraThm54Biholo)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open58 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX (ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only h21C) (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C h21C) ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed (ZInQ.Contrib.HCMWeierstrass.shimuraThm54_of_biholo hCM)) h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed (ZInQ.Contrib.HCMWeierstrass.shimuraThm54_of_biholo hCM)) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_hCMBiholo
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_hCMBiholo'
