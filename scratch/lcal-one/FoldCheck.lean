import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.TYZLcalOne

/-! lcal-one: the manual fold of variant B (tyz-genus) with `TYZLcalOne` proved. `h11` and `hL29` are top-level
arguments of `frozenTarget`, so autofold does not apply. For `Main.lean`: replace the two binders
`(h11 : TYZThm11Integral)` and `(hL29 : H29Split.TYZLemma29PrintedNe3)` by the one binder
`(h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)`; replace the argument `h11` by
`(ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only h21C)` and the argument `hL29` by
`(ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C h21C)`; add the import
`ZInQKernel.Contrib.OneProof.TYZLcalOne` (it imports `TYZThm11Genus`). TYZ hypotheses of `frozenTarget`: 2 → 1. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1 with `h11` and `hL29` replaced by TYZ Theorem 2.1 (complex sign choices)**: the body of
`frozenTarget`, written out with the two arguments changed (the proposed new `frozenTarget`). -/
theorem frozenTarget_lcalOne
    (r : HDec.HSyn.OpenResearchLeaves31) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open48 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX (ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only h21C)
      (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists
      (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C h21C) ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM)
      (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

/-- The same theorem, as an instance of the current `frozenTarget` (a check that nothing else changed). -/
theorem frozenTarget_lcalOne'
    (r : HDec.HSyn.OpenResearchLeaves31) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l (ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only h21C)
    (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C h21C) hCM h33 hBFH hGZ

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_lcalOne
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_lcalOne'
