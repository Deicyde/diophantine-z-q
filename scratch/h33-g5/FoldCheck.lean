import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.TYZThm33Adelic
import ZInQKernel.Contrib.OneProof.GrossZagierSplitUnique

/-! h33-g5 manual fold check: `ZInQ.OneProof.frozenTarget` (Main.lean at this branch's base) with the binder
`(h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)` replaced by `(h33a : ZInQ.H33G5.TYZThm33AdelicSome)` (TYZ Thm 3.3
with TYZ's adelic CM points `P_n = [h, 1] ∈ X_U(ℂ)`); alone, and together with h33-d1's `hGZ` fold. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- The `h33` fold alone (recommended for `h33`). -/
theorem _root_.ZInQ.H33G5.frozenTarget_g5
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33a : ZInQ.H33G5.TYZThm33AdelicSome)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open55 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX (ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only h21C) (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C h21C) ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM)
      (ZInQ.H33G5.tyzThm33_of_adelic (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33a))
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

/-- The fold is the old theorem composed with the contribution. -/
theorem _root_.ZInQ.H33G5.frozenTarget_g5_eq
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33a : ZInQ.H33G5.TYZThm33AdelicSome)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.H33G5.frozenTarget_g5 r t l h21C hCM h33a hBFH hGZ =
      ZInQ.OneProof.frozenTarget r t l h21C hCM
        (ZInQ.H33G5.tyzThm33_of_adelic (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33a) hBFH hGZ := rfl

/-- Both folds: `h33 ↦ h33a` (this task), `hGZ ↦ hGZss` (h33-d1). -/
theorem _root_.ZInQ.H33G5.frozenTarget_g5s
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33a : ZInQ.H33G5.TYZThm33AdelicSome)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZss : ZInQ.GZSplitUnique.GrossZagierCurveCdSplitSome) :
    ZInQ.FrozenTarget :=
  ZInQ.H33G5.frozenTarget_g5 r t l h21C hCM h33a hBFH
    (ZInQ.GZSplitUnique.grossZagierAlgOptCd_of_splitSome hGZss)

theorem _root_.ZInQ.H33G5.frozenTarget_g5s_eq
    (r : HDec.HSyn.OpenResearchLeaves38) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33a : ZInQ.H33G5.TYZThm33AdelicSome)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZss : ZInQ.GZSplitUnique.GrossZagierCurveCdSplitSome) :
    ZInQ.H33G5.frozenTarget_g5s r t l h21C hCM h33a hBFH hGZss =
      ZInQ.OneProof.frozenTarget r t l h21C hCM
        (ZInQ.H33G5.tyzThm33_of_adelic (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33a) hBFH
        (ZInQ.GZSplitUnique.grossZagierAlgOptCd_of_splitSome hGZss) := rfl

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.H33G5.frozenTarget_g5
#print axioms ZInQ.H33G5.frozenTarget_g5s
#print axioms ZInQ.H33G5.tyzThm33_of_adelic
#print axioms ZInQ.H33G5.tyzThm33AdelicSome_iff
#print axioms ZInQ.H33G5.isShPointAt_iff_exists
#print axioms ZInQ.H33G5.tyzEquiv
#print axioms ZInQ.H33G5.tyzToA_iTYZ
#print axioms ZInQ.H33G5.shFunEquiv
#print axioms ZInQ.H33G5.qExp_mem_X0Field
#print axioms ZInQ.AdelicX0.strong_approx
#print axioms ZInQ.AdelicX0.det_U0
#print axioms ZInQ.AdelicX0.gamma0OrbitsEquiv
#print axioms ZInQ.AdelicX0.f0_tyzP5
#print axioms ZInQ.AdelicX0.f0_tyzP7
