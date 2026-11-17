import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.GrossZagierCdPrinted

/-! gzcd-s1 manual fold check: `ZInQ.OneProof.frozenTarget` (Main.lean on this branch, top `sixContactMin_of_open63`)
with the binder `(hGZ : ZInQ.GZSch.GrossZagierCurveCd)` replaced by
`(hGZp : ZInQ.GZCdPrinted.GrossZagierCurveCdPrinted)` and its use `hGZ` by
`(ZInQ.GZCdPrinted.grossZagierCurveCd_of_printed hGZp)`. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, from every statement still open**, `hGZ` in printed form. -/
theorem _root_.ZInQ.GZCdPrinted.frozenTarget_printed
    (r : HDec.HSyn.OpenResearchLeaves44) (t : HDec.HSyn.OpenTextbookLeaves17) (l : HDec.HSyn.OpenAddedLeaves26)
    (h21S : ZInQ.Contrib.H21CSteps.TYZThm21Span)
    (hCM : ZInQ.Contrib.HCMLattice.ShimuraThm54Local)
    (h33a : ZInQ.H33Fix.TYZThm33Alg)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZp : ZInQ.GZCdPrinted.GrossZagierCurveCdPrinted) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open63 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX (ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only (ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S)) (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C (ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S)) ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMLattice.shimuraMainCM_of_local hCM) (ZInQ.H33Fix.tyzThm33_of_alg (ZInQ.Contrib.HCMLattice.shimuraMainCM_of_local hCM) h33a))
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMLattice.shimuraMainCM_of_local hCM) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg (ZInQ.GZSch.grossZagierAlgOptCd_of_curve (ZInQ.GZCdPrinted.grossZagierCurveCd_of_printed hGZp)) ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

/-- The fold is the current `frozenTarget` applied to the bridge. -/
theorem _root_.ZInQ.GZCdPrinted.frozenTarget_printed_eq
    (r : HDec.HSyn.OpenResearchLeaves44) (t : HDec.HSyn.OpenTextbookLeaves17) (l : HDec.HSyn.OpenAddedLeaves26)
    (h21S : ZInQ.Contrib.H21CSteps.TYZThm21Span)
    (hCM : ZInQ.Contrib.HCMLattice.ShimuraThm54Local)
    (h33a : ZInQ.H33Fix.TYZThm33Alg)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZp : ZInQ.GZCdPrinted.GrossZagierCurveCdPrinted) :
    ZInQ.GZCdPrinted.frozenTarget_printed r t l h21S hCM h33a hBFH hGZp =
      ZInQ.OneProof.frozenTarget r t l h21S hCM h33a hBFH
        (ZInQ.GZCdPrinted.grossZagierCurveCd_of_printed hGZp) := rfl

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.GZCdPrinted.frozenTarget_printed
#print axioms ZInQ.OneProof.frozenTarget
#print axioms ZInQ.GZCdPrinted.grossZagierCurveCd_iff_printed
#print axioms ZInQ.GZCdPrinted.grossZagierAlgOptCd_of_printed
#print axioms ZInQ.GZDiscr.discr_eq_of_sq
#print axioms ZInQ.GZDiscr.exists_sq_eq_discr
#print axioms ZInQ.CurveModel.exists_iso_of_functionField
#print axioms ZInQ.GZUnique.model_transfer
#print axioms ZInQ.H33D1.not_mem_chartZ_iff
#print axioms ZInQ.EpsSplit.quadChar_eq_epsD
