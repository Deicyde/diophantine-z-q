import ZInQKernel.OneProof.H.TailZ10

/-! # OneProof H, leaf-fold10: the bundles and `sixContactMin_of_open10`

The bundle `OpenTextbookLeaves10`, the map to leaf-fold9's `OpenTextbookLeaves9` and `sixContactMin_of_open10`.
The proof used is dimjac-glue's `ModularSplit.DimJac.dimJacobianEqGenus` (`TailZ10`), which fills the field
`dimJacobianEqGenus`. docs/research/leaf-fold10.md lists every field. -/

namespace HDec

namespace HSyn

/-! ## The bundles -/

/-- **The textbook leaves still open** (leaf-fold10): leaf-fold9's `OpenTextbookLeaves9` without
`dimJacobianEqGenus` (proved by dimjac-glue, `ModularSplit.DimJac.dimJacobianEqGenus`, `TailZ10`). 17 fields. -/
structure OpenTextbookLeaves10 : Prop where
  mulEtaleAbelianScheme : _root_.AvSplit.T4.MulEtaleAbelianScheme
  mumfordTorsionAlgClosed : _root_.AvSplit.MumfordTorsionAlgClosed
  homFreeFiniteAlgClosed : _root_.ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed
  charPolyIndepOfEllAlgClosed : _root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
  poincareComplement : _root_.ZInQ.Contrib.AVB1.PoincareComplement
  cartierSmooth : _root_.AVGlue.CartierSmooth
  geomConnOfRationalPoint : _root_.AVGlue.GeomConnOfRationalPoint
  groupSchemeEquidim : _root_.AVGlue.GroupSchemeEquidim
  t10 : _root_.T10Etale.T10_TateDuality
  uniformizationLeafAll : _root_.BPAnalytic.Uniformization.UniformizationLeafAll
  gagaMorphism : _root_.ZInQ.HomLattice.GAGAMorphism
  bdRInvariants : ∀ (p : ℕ) [Fact p.Prime], _root_.ZInQ.Contrib.HodgeSplit.BdRInvariants p
  yuThm11 : QMSplit.Yu.YuThm11
  genusX1Field : _root_.ZInQ.Contrib.CurvesG.GenusX1Field
  regularSmoothPerfect : _root_.CurveSplit.RegularSmoothPerfect
  igusaGL2 : _root_.ZInQ.RLeaf.IgusaGL2
  neronSchemeExtensionExists : _root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists

/-! ## From the new bundle to leaf-fold9's -/

/-- leaf-fold9's textbook bundle from leaf-fold10's: the field `dimJacobianEqGenus` is dimjac-glue's theorem. -/
theorem textbookLeaves9_of_open10 (t : OpenTextbookLeaves10) : OpenTextbookLeaves9 where
  mulEtaleAbelianScheme := t.mulEtaleAbelianScheme
  mumfordTorsionAlgClosed := t.mumfordTorsionAlgClosed
  homFreeFiniteAlgClosed := t.homFreeFiniteAlgClosed
  charPolyIndepOfEllAlgClosed := t.charPolyIndepOfEllAlgClosed
  poincareComplement := t.poincareComplement
  cartierSmooth := t.cartierSmooth
  geomConnOfRationalPoint := t.geomConnOfRationalPoint
  groupSchemeEquidim := t.groupSchemeEquidim
  t10 := t.t10
  uniformizationLeafAll := t.uniformizationLeafAll
  gagaMorphism := t.gagaMorphism
  bdRInvariants := t.bdRInvariants
  yuThm11 := t.yuThm11
  dimJacobianEqGenus := _root_.ModularSplit.DimJac.dimJacobianEqGenus
  genusX1Field := t.genusX1Field
  regularSmoothPerfect := t.regularSmoothPerfect
  igusaGL2 := t.igusaGL2
  neronSchemeExtensionExists := t.neronSchemeExtensionExists

/-- **G0 with only the open leaves and the open glue** (leaf-fold10; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from leaf-fold9's `OpenResearchLeaves9` (30), `OpenTextbookLeaves10` (17),
leaf-fold8's `OpenAddedLeaves8` (14) and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every
field is `docs/research/leaf-fold10.md` §2. -/
theorem sixContactMin_of_open10 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves8)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open9 r (textbookLeaves9_of_open10 t) l g

end HSyn

end HDec
