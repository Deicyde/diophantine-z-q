import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.TYZThm21Span

/-! h21c-steps: the hand fold of `h21C`. `h21C` is a top-level argument of `frozenTarget`, so autofold does not
apply. For `Main.lean`: replace the binder `(h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)` by
`(h21S : ZInQ.Contrib.H21CSteps.TYZThm21Span)`, replace both occurrences of the argument `h21C` by
`(ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S)`, and add the import
`ZInQKernel.Contrib.OneProof.TYZThm21Span` (it imports `TYZThm11Genus`). Fields of `frozenTarget`: unchanged in number
(h21C -> h21S). -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1 with `h21C` replaced by TYZ Theorem 2.1 over `π^U = ⊕ ℂ f_δ` (Theorem 2.4(1))**: the body of
`frozenTarget` with the argument changed (the proposed new `frozenTarget`). -/
theorem frozenTarget_h21S
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21S : ZInQ.Contrib.H21CSteps.TYZThm21Span)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open55 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX
      (ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only (ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S))
      (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists
      (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C (ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S))
      ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM)
      (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

/-- The same theorem, as an instance of the current `frozenTarget` (a check that nothing else changed). -/
theorem frozenTarget_h21S'
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21S : ZInQ.Contrib.H21CSteps.TYZThm21Span)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l (ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S) hCM h33 hBFH hGZ

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_h21S
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_h21S'
