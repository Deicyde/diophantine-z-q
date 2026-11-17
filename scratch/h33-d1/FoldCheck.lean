import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.TYZThm33Curve
import ZInQKernel.Contrib.OneProof.GrossZagierSplitUnique

/-! h33-d1 manual fold check: `ZInQ.OneProof.frozenTarget` (Main.lean at this branch's base) with the binder
`(h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)` replaced by `(h33c : ZInQ.H33D1.TYZThm33CurveSome)` and the
binder `(hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd)` replaced by `(hGZs : ZInQ.GZUnique.GrossZagierCurveCdSome)`;
each fold separately as well. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, from every statement still open** (both folds). -/
theorem _root_.ZInQ.H33D1.frozenTarget_d1
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33c : ZInQ.H33D1.TYZThm33CurveSome)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZs : ZInQ.GZUnique.GrossZagierCurveCdSome) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open55 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX (ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only h21C) (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C h21C) ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM)
      (ZInQ.H33D1.tyzThm33_of_curveSome (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33c))
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg (ZInQ.GZUnique.grossZagierAlgOptCd_of_some hGZs) ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

/-- The fold is the old theorem composed with the contributions. -/
theorem _root_.ZInQ.H33D1.frozenTarget_d1_eq
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33c : ZInQ.H33D1.TYZThm33CurveSome)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZs : ZInQ.GZUnique.GrossZagierCurveCdSome) :
    ZInQ.H33D1.frozenTarget_d1 r t l h21C hCM h33c hBFH hGZs =
      ZInQ.OneProof.frozenTarget r t l h21C hCM
        (ZInQ.H33D1.tyzThm33_of_curveSome (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33c) hBFH
        (ZInQ.GZUnique.grossZagierAlgOptCd_of_some hGZs) := rfl

/-- The `h33` fold alone. -/
theorem _root_.ZInQ.H33D1.frozenTarget_h33c
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33c : ZInQ.H33D1.TYZThm33CurveSome)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l h21C hCM
    (ZInQ.H33D1.tyzThm33_of_curveSome (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33c) hBFH hGZ

/-- The `hGZ` fold alone. -/
theorem _root_.ZInQ.H33D1.frozenTarget_hGZs
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZs : ZInQ.GZUnique.GrossZagierCurveCdSome) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l h21C hCM h33 hBFH (ZInQ.GZUnique.grossZagierAlgOptCd_of_some hGZs)

/-- **Recommended fold**: `h33 ↦ h33c : TYZThm33CurveSome`, `hGZ ↦ hGZss : GrossZagierCurveCdSplitSome`
(one model, twist by splitting in `K`: S1 and the `ε_D` step both removed). -/
theorem _root_.ZInQ.H33D1.frozenTarget_d1s
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33c : ZInQ.H33D1.TYZThm33CurveSome)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZss : ZInQ.GZSplitUnique.GrossZagierCurveCdSplitSome) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open55 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX (ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only h21C) (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C h21C) ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM)
      (ZInQ.H33D1.tyzThm33_of_curveSome (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33c))
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg (ZInQ.GZSplitUnique.grossZagierAlgOptCd_of_splitSome hGZss) ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

theorem _root_.ZInQ.H33D1.frozenTarget_d1s_eq
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33c : ZInQ.H33D1.TYZThm33CurveSome)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZss : ZInQ.GZSplitUnique.GrossZagierCurveCdSplitSome) :
    ZInQ.H33D1.frozenTarget_d1s r t l h21C hCM h33c hBFH hGZss =
      ZInQ.OneProof.frozenTarget r t l h21C hCM
        (ZInQ.H33D1.tyzThm33_of_curveSome (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33c) hBFH
        (ZInQ.GZSplitUnique.grossZagierAlgOptCd_of_splitSome hGZss) := rfl

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.H33D1.frozenTarget_d1
#print axioms ZInQ.H33D1.frozenTarget_d1s
#print axioms ZInQ.GZSplitUnique.grossZagierAlgOptCd_of_splitSome
#print axioms ZInQ.H33D1.tyzThm33Curve_of_some
#print axioms ZInQ.H33D1.tyzThm33Curve_hyps_satisfiable
#print axioms ZInQ.H33D1.tyzThm33_of_curveSome
#print axioms ZInQ.GZUnique.grossZagierAlgOptCd_of_some
#print axioms ZInQ.GZUnique.grossZagierCurveCd_of_some
#print axioms ZInQ.CurveModel.exists_iso_of_functionField
#print axioms ZInQ.H33D1.valuationRing_stalk_ESch
#print axioms ZInQ.H33D1.tyzThm33CurveSome_of_all
