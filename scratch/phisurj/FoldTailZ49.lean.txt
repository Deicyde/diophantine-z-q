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

#print axioms HDec.HSyn.sixContactMin_of_open42
