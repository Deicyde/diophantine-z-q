import ZInQKernel.OneProof.H.TailZ48
import ZInQKernel.Contrib.OneProof.NeronGoodModelIso

/-! # OneProof H, fold33-combine (goodmodel-iso, fold G): `sixContactMin_of_open42` (written by hand after autofold's pattern)

goodmodel-iso's fold G replaces the research field `mumfordGroupLawConn` (GIT Thm 6.14 over a connected base) and the
textbook field `neronSchemeExtensionExists` (BLR 1.4 Thm 3, number-field case) by the one printed leaf
`neronSchemeExtensionDedekind` (BLR 1.4 Thm 3 over an affine Dedekind scheme, existence half). The research side is in
place (`mumfordGroupLaw` narrowed to `MumfordGroupLawDVR` in `OpenResearchLeaves14`-`27`; the field swapped in
`OpenResearchLeaves28`, `29`; `GoodModelIso.mumfordGroupLawDVR_of_dedekind`). The textbook side is this module:
`OpenTextbookLeaves16` is `OpenTextbookLeaves15` without `neronSchemeExtensionExists`, which
`GroupLawNeron.neronSchemeExtensionExists_of_dedekind` supplies from the research leaf. Net −1, no new glue. -/

namespace HDec

namespace HSyn

/-- `OpenTextbookLeaves15` without `neronSchemeExtensionExists` (fold33-combine, goodmodel-iso). -/
structure OpenTextbookLeaves16 : Prop where
  mumfordTorsionAlgClosed : _root_.AvSplit.MumfordTorsionAlgClosed
  charPolyIndepOfEllAlgClosed : _root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
  gagaMorphism : _root_.ZInQ.HomLattice.GAGAMorphism

/-- `OpenTextbookLeaves15` from `OpenTextbookLeaves16` and BLR 1.4 Thm 3 over Dedekind schemes
(`neronSchemeExtensionExists_of_dedekind`). -/
theorem openTextbookLeaves15_of_OpenTextbookLeaves16 (n : OpenTextbookLeaves16)
    (h : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind) : OpenTextbookLeaves15 where
  mumfordTorsionAlgClosed := n.mumfordTorsionAlgClosed
  charPolyIndepOfEllAlgClosed := n.charPolyIndepOfEllAlgClosed
  gagaMorphism := n.gagaMorphism
  neronSchemeExtensionExists := _root_.ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind h

/-- **G0 with only the open leaves** (fold33-combine; `mumfordGroupLawConn` and `neronSchemeExtensionExists` replaced
by `neronSchemeExtensionDedekind`). -/
theorem sixContactMin_of_open42 (r : OpenResearchLeaves29) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves20) : ZInQ.SixContactMin :=
  sixContactMin_of_open41 r (openTextbookLeaves15_of_OpenTextbookLeaves16 t r.neronSchemeExtensionDedekind) l

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open42
