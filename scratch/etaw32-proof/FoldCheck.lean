import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.EtaW32Character

/-!
# etaw32-proof: the manual fold of `Main.lean` without `hW`

`ZInQ.OneProof.frozenTarget_etaW32` is `ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean` at
`0e3c3125`) with the binder `hW : ZInQ.CdOpt.EtaW32Character` removed and filled by
`ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof`; the body is Main's, verbatim otherwise.
`frozenTarget_etaW32'` checks it against Main's theorem itself.
-/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, from every statement still open**, with `hW` (`ZInQ.CdOpt.EtaW32Character`) proved
(`ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof`). -/
theorem _root_.ZInQ.OneProof.frozenTarget_etaW32
    (r : HDec.HSyn.OpenResearchLeaves29) (t : HDec.HSyn.OpenTextbookLeaves15) (l : HDec.HSyn.OpenAddedLeaves20)
    (h11 : TYZThm11Integral)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) (hQ : ZInQ.GZAlg.Gamma0QExpansion) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open41 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof hfx hL29 ZInQ.Contrib.T21Proof.tyzThm21At31 hP23) hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed hCM (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ hQ
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

/-- The same, derived from Main's `frozenTarget` directly. -/
theorem ZInQ.OneProof.frozenTarget_etaW32'
    (r : HDec.HSyn.OpenResearchLeaves29) (t : HDec.HSyn.OpenTextbookLeaves15) (l : HDec.HSyn.OpenAddedLeaves20)
    (h11 : ZInQ.Contrib.TYZDecomp.TYZThm11Integral)
    (hfx : ZInQ.Contrib.TYZDecomp.H29Split.TYZTestVectorExists)
    (hL29 : ZInQ.Contrib.TYZDecomp.H29Split.TYZLemma29PrintedNe3)
    (hP23 : ZInQ.Contrib.TYZDecomp.H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) (hQ : ZInQ.GZAlg.Gamma0QExpansion) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l h11 hfx hL29 hP23 hCM h33 hBFH hGZ hQ
    ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof

#print axioms ZInQ.OneProof.frozenTarget_etaW32
#print axioms ZInQ.OneProof.frozenTarget_etaW32'
