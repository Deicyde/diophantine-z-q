import ZInQKernel.OneProof.H.TailZ51
import ZInQKernel.Contrib.OneProof.PhiAmpleIsogenyOpen

/-! # OneProof H, fold33-pic (phisurj): `sixContactMin_of_open45` (reroute by bypass to an older generation)

phisurj removes the added field `mumfordPhiSurjectiveAC` (Mumford §8 Thm 1 over `k = k̄`) without proving it. Its
only readers on the route of `sixContactMin_of_open44` are the two maps that compute `T09Pic.PhiAmpleIsogeny` from it,
`openAddedLeaves18_of_OpenAddedLeaves19` (TailZ45) and the poincare conversion
`openTextbookLeaves13_of_OpenTextbookLeaves14_hf` (homfree reroute), each through
`PicFix.phiAmpleIsogeny_of_printed l.mumfordKLFiniteSectionAC l.mumfordPhiSurjectiveAC`. `PhiAmpleIsogeny` is now
`PhiSurj.phiAmpleIsogeny_of_open` from L1, L2 and the textbook leaf `mumfordTorsionAlgClosed`. So this module enters
the existing chain at the generation `OpenAddedLeaves18`, whose field is `phiAmpleIsogeny` itself, through the
existing `sixContactMin_of_open37_hf_gm` (`GoodModelIsoCopy`); no declaration is copied and none is changed.
`weilPairingMumford` (removed by TailZ51) is filled in the same way by `PhiSurj.weilPairingMumford_of_open`. Net −1,
no new leaf. -/

namespace HDec

namespace HSyn

/-- `OpenAddedLeaves21` without `mumfordPhiSurjectiveAC` (fold33-pic, phisurj: rerouted, its readers need only
`PhiAmpleIsogeny`, proved by `PhiSurj.phiAmpleIsogeny_of_open`). -/
structure OpenAddedLeaves22 : Prop where
  /-- t09-pic, L1, printed form: the relative Picard fppf sheaf of an abelian variety over a field is representable
  (Murre 1964, Oort 1962; FGA Exp. 232 Thm 3.1; Kleiman, *The Picard scheme*, Thm 9.4.8 with 9.2.5; locators
  UNVERIFIED). With the next three replaces `t09SymmIsogenyExists`. -/
  picRepresentableAbVar : _root_.T09Pic.PicRepresentableAbVar
  /-- t09-pic, L2, printed form: for every representation of `Pic_{A/K}`, its identity component with the induced
  group law is an abelian variety (`IsPicZero`; Mumford §13, Kleiman 9.5.1 and 9.5.3, SGA 3 VI_A 2.4; locators
  UNVERIFIED). -/
  picZeroAbVar : _root_.T09Pic.PicZeroAbVar

/-- `OpenAddedLeaves18` (the generation whose field is `phiAmpleIsogeny`) from `OpenAddedLeaves22` and the textbook
torsion leaf: `phiAmpleIsogeny` by `PhiSurj.phiAmpleIsogeny_of_open`, `weilPairingMumford` by
`PhiSurj.weilPairingMumford_of_open`, `egaIV_8_10_5_xii` as in `openAddedLeaves18_of_OpenAddedLeaves19`. -/
theorem openAddedLeaves18_of_OpenAddedLeaves22 (t : OpenTextbookLeaves16) (n : OpenAddedLeaves22) :
    OpenAddedLeaves18 where
  egaIV_8_10_5_xii := _root_.ZInQ.Contrib.EGAProperLimit.egaIV_8_10_5_xii_proof
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := n.picZeroAbVar
  phiAmpleIsogeny := _root_.PhiSurj.phiAmpleIsogeny_of_open n.picRepresentableAbVar n.picZeroAbVar
    t.mumfordTorsionAlgClosed
  weilPairingMumford := _root_.PhiSurj.weilPairingMumford_of_open n.picRepresentableAbVar n.picZeroAbVar
    t.mumfordTorsionAlgClosed

/-- `OpenTextbookLeaves13HF` from `OpenTextbookLeaves16`, BLR 1.4 Thm 3 over Dedekind schemes and
`OpenAddedLeaves22` (as `openTextbookLeaves13_of_OpenTextbookLeaves14_hf`, with `PhiAmpleIsogeny` from
`PhiSurj.phiAmpleIsogeny_of_open`). -/
theorem openTextbookLeaves13HF_of_open16_22 (t : OpenTextbookLeaves16)
    (h : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind) (l : OpenAddedLeaves22) :
    OpenTextbookLeaves13HF where
  mumfordTorsionAlgClosed := t.mumfordTorsionAlgClosed
  homFreeFiniteAlgClosed := _root_.ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteC _root_.uniformizationLeafAll_proof
    t.mumfordTorsionAlgClosed
  charPolyIndepOfEllAlgClosed := t.charPolyIndepOfEllAlgClosed
  poincareComplement := _root_.ZInQ.Contrib.OneProof.PoincareComplement.poincareComplement_of_open
    l.picRepresentableAbVar l.picZeroAbVar
    (_root_.PhiSurj.phiAmpleIsogeny_of_open l.picRepresentableAbVar l.picZeroAbVar t.mumfordTorsionAlgClosed)
    _root_.ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof
    _root_.ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof
  gagaMorphism := t.gagaMorphism
  neronSchemeExtensionExists := _root_.ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind h

/-- **G0 with only the open leaves** (fold33-pic, phisurj; `mumfordPhiSurjectiveAC` rerouted, `weilPairingMumford`
proved). -/
theorem sixContactMin_of_open45 (r : OpenResearchLeaves31) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves22) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open37_hf_gm
    (openResearchLeaves27_of_OpenResearchLeaves28_gm
      (openResearchLeaves28_of_OpenResearchLeaves29_gm (openResearchLeaves29GM_of_OpenResearchLeaves31 r)))
    (openTextbookLeaves13HF_of_open16_22 t r.neronSchemeExtensionDedekind l)
    (openAddedLeaves18_of_OpenAddedLeaves22 t l)

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open45
