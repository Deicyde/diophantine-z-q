import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.H.TailZ48
import ZInQKernel.Contrib.OneProof.WeilPairingMumfordOpen

/-! # OneProof H, phisurj: `sixContactMin_of_open42` (hand fold, after leaf-fold33's reroute pattern)

Field removed: `mumfordPhiSurjectiveAC` (Mumford §8 Thm 1 over `k = k̄`). It is not filled: its only readers
(TailZ45:123 and the poincare conversion, TailZ46:104 / HomFreeFiniteAlgClosedReroute:2082) read
`PicFix.phiAmpleIsogeny_of_printed l.mumfordKLFiniteSectionAC l.mumfordPhiSurjectiveAC : T09Pic.PhiAmpleIsogeny`,
which is now `PhiSurj.phiAmpleIsogeny_of_open l.picRepresentableAbVar l.picZeroAbVar t.mumfordTorsionAlgClosed`. The route below is
`sixContactMin_of_open41 → open40_hf → open39_hf → open38_hf → open37_hf` with that one term changed.
Field removed (proved): `weilPairingMumford`, by `PhiSurj.weilPairingMumford_of_open l.picRepresentableAbVar
l.picZeroAbVar t.mumfordTorsionAlgClosed`. No new leaf. -/

namespace HDec

namespace HSyn

/-- `OpenAddedLeaves20` without `mumfordPhiSurjectiveAC` (rerouted) and `weilPairingMumford` (proved) (phisurj). -/
structure OpenAddedLeaves21 : Prop where
  /-- t09-pic, L1, printed form (unchanged). -/
  picRepresentableAbVar : _root_.T09Pic.PicRepresentableAbVar
  /-- t09-pic, L2, printed form (unchanged). -/
  picZeroAbVar : _root_.T09Pic.PicZeroAbVar

/-- `OpenAddedLeaves18` (the generation with the field `phiAmpleIsogeny`) from `OpenAddedLeaves21` and the
textbook bundle: `phiAmpleIsogeny` by `PhiSurj.phiAmpleIsogeny_of_open`, `weilPairingMumford` by
`PhiSurj.weilPairingMumford_of_open`. -/
theorem openAddedLeaves18_of_OpenAddedLeaves21 (t : OpenTextbookLeaves15) (n : OpenAddedLeaves21) :
    OpenAddedLeaves18 where
  egaIV_8_10_5_xii := _root_.ZInQ.Contrib.EGAProperLimit.egaIV_8_10_5_xii_proof
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := n.picZeroAbVar
  phiAmpleIsogeny := _root_.PhiSurj.phiAmpleIsogeny_of_open n.picRepresentableAbVar n.picZeroAbVar t.mumfordTorsionAlgClosed
  weilPairingMumford := _root_.PhiSurj.weilPairingMumford_of_open n.picRepresentableAbVar n.picZeroAbVar
    t.mumfordTorsionAlgClosed

/-- `OpenTextbookLeaves13HF` from `OpenTextbookLeaves15` and `OpenAddedLeaves21` (as
`openTextbookLeaves13_of_OpenTextbookLeaves14_hf`, with `PhiAmpleIsogeny` from `phiAmpleIsogeny_of_open`). -/
theorem openTextbookLeaves13HF_of_open15_21 (t : OpenTextbookLeaves15) (l : OpenAddedLeaves21) :
    OpenTextbookLeaves13HF where
  mumfordTorsionAlgClosed := t.mumfordTorsionAlgClosed
  homFreeFiniteAlgClosed := _root_.ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteC _root_.uniformizationLeafAll_proof t.mumfordTorsionAlgClosed
  charPolyIndepOfEllAlgClosed := t.charPolyIndepOfEllAlgClosed
  poincareComplement := _root_.ZInQ.Contrib.OneProof.PoincareComplement.poincareComplement_of_open l.picRepresentableAbVar l.picZeroAbVar (_root_.PhiSurj.phiAmpleIsogeny_of_open l.picRepresentableAbVar l.picZeroAbVar t.mumfordTorsionAlgClosed) _root_.ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof _root_.ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof
  gagaMorphism := t.gagaMorphism
  neronSchemeExtensionExists := t.neronSchemeExtensionExists

/-- **G0 with only the open leaves** (phisurj; `mumfordPhiSurjectiveAC` rerouted). -/
theorem sixContactMin_of_open42 (r : OpenResearchLeaves29) (t : OpenTextbookLeaves15) (l : OpenAddedLeaves21) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open37_hf
    (openResearchLeaves27_of_OpenResearchLeaves28 (openResearchLeaves28_of_OpenResearchLeaves29 r))
    (openTextbookLeaves13HF_of_open15_21 t l) (openAddedLeaves18_of_OpenAddedLeaves21 t l)

end HSyn

end HDec


namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- `ZInQ.OneProof.frozenTarget` with the added bundle `OpenAddedLeaves21` (no `mumfordPhiSurjectiveAC`); the
body is Main's with `sixContactMin_of_open41 r t l` replaced by `sixContactMin_of_open42 r t l`. -/
theorem frozenTarget_phisurj
    (r : HDec.HSyn.OpenResearchLeaves29) (t : HDec.HSyn.OpenTextbookLeaves15) (l : HDec.HSyn.OpenAddedLeaves21)
    (h11 : TYZThm11Integral)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) (hQ : ZInQ.GZAlg.Gamma0QExpansion) (hW : ZInQ.CdOpt.EtaW32Character) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open42 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof hfx hL29 ZInQ.Contrib.T21Proof.tyzThm21At31 hP23) hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed hCM (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ hQ hW)
      ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_phisurj
