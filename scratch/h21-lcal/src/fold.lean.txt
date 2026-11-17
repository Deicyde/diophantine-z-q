
/-! # h21-lcal: the hand fold of `h21C` (a top-level argument of `frozenTarget`)

Variant A (current `Main.lean`): replace the binder `(h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)` by
`(h21P : ZInQ.Contrib.H21Lcal.TYZThm21PairsPrinted)` and both occurrences of the argument `h21C` by
`(ZInQ.Contrib.H21Lcal.tyzThm21PairsC_of_printed h21P)`.
Variant B (after h21c-steps' fold `h21C -> h21S`): replace `(h21S : ZInQ.Contrib.H21CSteps.TYZThm21Span)` by
`(h21SP : ZInQ.Contrib.H21Lcal.TYZThm21SpanPrinted)` and `(ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S)` by
`(ZInQ.Contrib.H21Lcal.tyzThm21PairsC_of_spanPrinted h21SP)`.
Either way add the import of the module holding this file's development. Fields of `frozenTarget`: unchanged in
number. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Variant A**: the body of `frozenTarget` with `h21C` replaced by TYZ Theorem 2.1 over TYZ's printed `𝓛`. -/
theorem frozenTarget_h21P
    (r : HDec.HSyn.OpenResearchLeaves42) (t : HDec.HSyn.OpenTextbookLeaves17) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21P : ZInQ.Contrib.H21Lcal.TYZThm21PairsPrinted)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33a : ZInQ.H33Fix.TYZThm33Alg)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZSch.GrossZagierCurveCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open60 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX (ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only (ZInQ.Contrib.H21Lcal.tyzThm21PairsC_of_printed h21P)) (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C (ZInQ.Contrib.H21Lcal.tyzThm21PairsC_of_printed h21P)) ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) (ZInQ.H33Fix.tyzThm33_of_alg (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33a))
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg (ZInQ.GZSch.grossZagierAlgOptCd_of_curve hGZ) ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

/-- Variant A through the current `frozenTarget` (nothing else changed). -/
theorem frozenTarget_h21P'
    (r : HDec.HSyn.OpenResearchLeaves42) (t : HDec.HSyn.OpenTextbookLeaves17) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21P : ZInQ.Contrib.H21Lcal.TYZThm21PairsPrinted)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33a : ZInQ.H33Fix.TYZThm33Alg)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZSch.GrossZagierCurveCd) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l (ZInQ.Contrib.H21Lcal.tyzThm21PairsC_of_printed h21P) hCM h33a hBFH hGZ

/-- **Variant B** (on top of h21c-steps): `h21S` replaced by the span form over TYZ's printed `𝓛`. -/
theorem frozenTarget_h21SP
    (r : HDec.HSyn.OpenResearchLeaves42) (t : HDec.HSyn.OpenTextbookLeaves17) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21SP : ZInQ.Contrib.H21Lcal.TYZThm21SpanPrinted)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33a : ZInQ.H33Fix.TYZThm33Alg)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZSch.GrossZagierCurveCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open60 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX (ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only (ZInQ.Contrib.H21Lcal.tyzThm21PairsC_of_spanPrinted h21SP)) (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C (ZInQ.Contrib.H21Lcal.tyzThm21PairsC_of_spanPrinted h21SP)) ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) (ZInQ.H33Fix.tyzThm33_of_alg (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33a))
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg (ZInQ.GZSch.grossZagierAlgOptCd_of_curve hGZ) ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

/-- Variant B through the current `frozenTarget`. -/
theorem frozenTarget_h21SP'
    (r : HDec.HSyn.OpenResearchLeaves42) (t : HDec.HSyn.OpenTextbookLeaves17) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21SP : ZInQ.Contrib.H21Lcal.TYZThm21SpanPrinted)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33a : ZInQ.H33Fix.TYZThm33Alg)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZSch.GrossZagierCurveCd) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l (ZInQ.Contrib.H21Lcal.tyzThm21PairsC_of_spanPrinted h21SP) hCM h33a hBFH hGZ

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_h21P
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_h21P'
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_h21SP
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_h21SP'
