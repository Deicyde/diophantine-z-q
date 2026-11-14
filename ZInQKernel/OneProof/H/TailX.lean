import ZInQKernel.OneProof.H.TailO
import ZInQKernel.OneProof.H.TailP
import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.OneProof.H.TailR
import ZInQKernel.OneProof.H.TailU
import ZInQKernel.OneProof.H.TailV
import ZInQKernel.OneProof.H.TailW

/-! # OneProof H, leaf-fold7: the next bundle generation

`HDec.HSyn.sixContactMin_of_open7 (r : OpenResearchLeaves7) (t : OpenTextbookLeaves7) (l : OpenAddedLeaves7)
(g : OpenGlue7)` proves `ZInQ.SixContactMin` by filling leaf-fold6's bundles (`sixContactMin_of_open6`, `TailO`)
from the new ones. Folded (docs/research/leaf-fold7.md lists every field):

* av-glue (`TailP`): `t8` (T8) from `PoincareComplement`, `CartierSmooth`, `GeomConnOfRationalPoint`,
  `GroupSchemeEquidim` and the quasi-inverse of an isogeny;
* av-split (`TailQ`): `t4`, `t5`, `t35`, `homLatticeCorr`, `isogenyQuasiInverse` from `MulEtaleAbelianScheme`,
  `MumfordTorsionAlgClosed`, `UniformizationLeafAll`, `GAGAMorphism`, `MilneIsogenyQuasiInverse`;
* curve-split (`TailR`): `curveBijIso` proved (dropped), `normalCurveSmoothQ` from `RegularSmoothPerfect`,
  `geomConnectedOfConstantFieldQ` from the field `zariskiConnectedness` (dropped);
* qm-split (`TailU`): `qmClassNumberOne` proved (dropped), `t27` from `YuThm11`, `cmOptimalEmbedding`,
  `qmAutCard`, `alFixedPoints` from `QMCentralizerCMC` (with T11(b)), `stQM` from `ShimuraTaniyamaQbar`, `r4` from
  `IgusaPsi4` and `IgusaChi10`, `r1b` from `ShimuraFamily`;
* hodge-split (`TailS`, `TailT`, transports in `TailV`): `r14` from Diamond–Shurman's Thms 9.6.5-9.6.6, `t23` from
  `B_dR^{G_{ℚ_p}} = ℚ_p`, `senTwist` and `finiteImageHT` from Tate's two theorems on `ℂ_p(i)^{G_K}`;
* mcr-glue (`TailW`): the glue `ModelCoordinateResidue` from the smaller glue `QuotientP1Coordinate`.

No existing module is edited; every field that is not folded keeps leaf-fold6's type. -/

namespace HDec

set_option maxHeartbeats 1000000

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ## Transports between the split tasks' copies and the chain's constants

Each split task copied its row verbatim over the kernel (or over leaf-fold4's chain); the chain's field has the same
text over the same constants (op-dedupe made the chain's names aliases of the kernel's), so each transport is the
identity up to unfolding. -/

/-- curve-split's root copy of `ModelGlue.CurveBijIso` is the chain's row (same text over `LeafQM.AV.fieldPt`,
`LeafQM.AV.Qbar`). -/
theorem curveBijIso_lf7 : ModelGlue.CurveBijIso := _root_.CurveSplit.curveBijIso

/-- av-split's root copy of `WeilPairing.IsogenyQuasiInverse` gives the chain's row. -/
theorem isogenyQuasiInverse_lf7 (h : _root_.AvSplit.MilneIsogenyQuasiInverse) : WeilPairing.IsogenyQuasiInverse :=
  _root_.AvSplit.Final.h54 h

/-- av-split's root copy of `WeilPairing.IsogenyQuasiInverse` gives av-glue's copy. -/
theorem isogenyQuasiInverseAG_lf7 (h : _root_.AvSplit.MilneIsogenyQuasiInverse) :
    _root_.AVGlue.WeilPairing.IsogenyQuasiInverse :=
  _root_.AvSplit.Final.h54 h

/-- qm-split's copy of `STQM` is leafq-check's row. -/
theorem stQM_lf7 (h : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar) :
    G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM :=
  G0Split.FibreQM.PeriodMapH.QMSplitSTQM.stqm_of h

/-! ## The bundles -/

/-- **The research leaves still open** (leaf-fold7): leaf-fold5's `OpenResearchLeaves5` with `r4` replaced by
Igusa's two modularity statements, `r1b` by `ShimuraFamily` (qm-split) and `r14` by Diamond–Shurman's two theorems
(hodge-split). 28 fields. -/
structure OpenResearchLeaves7 : Prop where
  r1r2 : LeafAdopt.R1R2fpRep
  /-- qm-split, H-20: Shimura 1967 Main Thm I on one fine witness, for every map `π : Y → P¹` (replaces `r1b`). -/
  shimuraFamily : QMSplit.Moduli.ShimuraFamily
  r1rec : LeafQM.AV.R1rec
  r3 : _root_.ZInQ.LeafPush2.R03_LinYang
  /-- qm-split, H-2: Igusa's `ψ₄` is a Siegel modular form of weight 4 (with `igusaChi10`, replaces `r4`). -/
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  /-- qm-split, H-2: Igusa's `χ₁₀` is a Siegel modular form of weight 10. -/
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r5 : LeafQM.AV.R5fp
  r5count : LeafQM.AV.R5fpCount
  r6 : _root_.PkgI2.RaynaudCriterion.{0}
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r7b : _root_.PkgI2.SerreTatePotentialGood.{0}
  r8 : _root_.PkgI2.GrothendieckMonodromy.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  r10 : PkgI4.DeRhamComparisonHT
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  /-- hodge-split, H-22: Diamond–Shurman Thm 9.6.5 (`k ≥ 2`, Deligne; with `dsThm966`, replaces `r14`). -/
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  /-- hodge-split, H-22: Diamond–Shurman Thm 9.6.6 (`k = 1`, Deligne–Serre Thm 4.1). -/
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r15 : DeligneSerreConseq
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r20 : ZInQ.DefFaltings.R20_FaltingsLemma5
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  h5fin : ZInQ.DefFaltings.StableHeightFinite

/-- **The textbook leaves still open** (leaf-fold7): leaf-fold6's `OpenTextbookLeaves6` with T4, T5, T8, T35,
`homLatticeCorr`, T27 and the two curve composites replaced by published-form leaves, and
`geomConnectedOfConstantFieldQ` dropped (a theorem from the added field `zariskiConnectedness`), and T23 replaced
by `B_dR^{G_{ℚ_p}} = ℚ_p`. 23 fields. -/
structure OpenTextbookLeaves7 : Prop where
  t3Surj : _root_.ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj.{0}
  /-- av-split, H-24: `[m]` on an abelian scheme over `Spec O` is étale when `m ∈ O×` (replaces `t4`). -/
  mulEtaleAbelianScheme : _root_.AvSplit.T4.MulEtaleAbelianScheme
  /-- av-split, H-25: `A(k)[n] ≅ (ℤ/n)^{2g}` over an algebraically closed `k`, `char k ∤ n` (replaces `t5`). -/
  mumfordTorsionAlgClosed : _root_.AvSplit.MumfordTorsionAlgClosed
  homFreeFiniteAlgClosed : _root_.ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed
  charPolyIndepOfEllAlgClosed : _root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
  /-- av-b1, H-72: Poincaré's complete reducibility, complement form (with the next three, replaces `t8`). -/
  poincareComplement : _root_.ZInQ.Contrib.AVB1.PoincareComplement
  /-- av-glue: Cartier's theorem (a group scheme locally of finite type over a field of characteristic 0 is
  smooth). -/
  cartierSmooth : _root_.AVGlue.CartierSmooth
  /-- av-glue: Stacks 04KV (connected, finite type, with a rational point ⇒ geometrically connected). -/
  geomConnOfRationalPoint : _root_.AVGlue.GeomConnOfRationalPoint
  /-- av-glue: a group scheme of finite type over a field is equidimensional (SGA 3 VI_A 2.4). -/
  groupSchemeEquidim : _root_.AVGlue.GroupSchemeEquidim
  t10 : _root_.T10Etale.T10_TateDuality
  /-- bp-analytic's AN3 leaf (kernel), Mumford §1 for `A^an` in coordinate form (with the next, replaces
  `homLatticeCorr`; with `mumfordTorsionAlgClosed`, replaces `t35`). -/
  uniformizationLeafAll : _root_.BPAnalytic.Uniformization.UniformizationLeafAll
  /-- homlattice, via av-split, H-69: GAGA for homomorphisms of complex abelian varieties. -/
  gagaMorphism : _root_.ZInQ.HomLattice.GAGAMorphism
  t11bExists : AVB2.T11bExists
  /-- hodge-split, H-32: `B_dR^{G_{ℚ_p}} = ℚ_p` (Fontaine, Astérisque 223 Exp. II; replaces `t23`). -/
  bdRInvariants : ∀ (p : ℕ) [Fact p.Prime], _root_.ZInQ.Contrib.HodgeSplit.BdRInvariants p
  t24 : _root_.PkgI4.EigenformTwist
  /-- qm-split, H-35: Yu 2013 Thm 1.1 with its splitting clause (replaces `t27`). -/
  yuThm11 : QMSplit.Yu.YuThm11
  t33 : _root_.LeafModCurves.JacobianExists ℚ
  dimJacobianEqGenus : _root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus
  genusX1Field : _root_.ZInQ.Contrib.CurvesG.GenusX1Field
  normalModelOfFunctionFieldQ : _root_.ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ
  /-- curve-split, H-81: Stacks 00TV (regular ⇒ smooth over a perfect field; replaces `normalCurveSmoothQ`). -/
  regularSmoothPerfect : _root_.CurveSplit.RegularSmoothPerfect
  x0Transitive : _root_.ZInQ.RLeaf.X0Transitive
  neronSchemeExtensionExists : _root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists

/-- **The added leaves still open** (leaf-fold7): leaf-fold6's `OpenAddedLeaves6` without `qmClassNumberOne` and
`curveBijIso` (proved), with the three QM computations replaced by `QMCentralizerCMC`, `stQM` by
`ShimuraTaniyamaQbar`, `isogenyQuasiInverse` by `MilneIsogenyQuasiInverse`, and `senTwist`, `finiteImageHT` by
Tate's two theorems. 16 fields. -/
structure OpenAddedLeaves7 : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmHauptmodulBase3 : LeafQCheck.HM.QMHauptmodulBase3
  /-- qm-split, H-42/H-61/H-63: `End_𝒪(A)` of a QM surface over `ℂ` is `ℤ` or an optimally embedded order of an
  imaginary quadratic field (replaces `cmOptimalEmbedding`, `qmAutCard`, `alFixedPoints`). -/
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  /-- hodge-split, H-51/H-52/H-8: Tate 1967 §3.3 Thm 2, `ℂ_p(i)^{G_K} = 0` for `i ≠ 0` (with `axSenTate`, replaces
  `senTwist` and `finiteImageHT`). -/
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  /-- hodge-split: Ax–Sen–Tate, `ℂ_p^{G_K} = K` (Tate 1967 §3.3 Thm 1; Sen 1969; Ax 1970). -/
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  /-- av-split, H-54: Milne's quasi-inverse of an isogeny, as morphisms (replaces `isogenyQuasiInverse`). -/
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  x6ConicModel : X6Kummer.X6ConicModel
  y3Connected : TSHecke.Y3Connected
  zariskiConnectedness : _root_.ZariskiConn.ZariskiConnectedness.{0}
  /-- qm-split, H-86: Shimura–Taniyama, a CM abelian variety over `ℂ` has a model over `ℚ̄` (replaces `stQM`). -/
  shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar
  valenceFormulaGammaStar : LeafQCheck.VB.ValenceFormulaGammaStar
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii
  shimuraGoodReduction : VertWitness.ShimuraGoodReduction

/-- **The glue still open** (leaf-fold7): mcr-glue's `QuotientP1Coordinate` (the coordinate of the tame quotient
`𝒴/Γ' ≅ P¹_{ℤ_(p)}` as a finite map with the fibre relation; the residue clause of `ModelCoordinateResidue` is
proved, `MCRGlue.modelCoordinateResidue_of_quotient'`). -/
structure OpenGlue7 : Prop where
  /-- mcr-glue: a finite `q : 𝒴 → 𝒵` over `ℤ_(p)` and an isomorphism `𝒵 ≅ P¹_{ℤ_(p)}` by charts whose composite
  has R2fp's fibre relation (replaces `modelCoordinateResidue`). -/
  quotientP1Coordinate : MCRGlue.QuotientP1Coordinate

/-! ## From the new bundles to leaf-fold6's -/

/-- leaf-fold6's research bundle (`OpenResearchLeaves5`) from leaf-fold7's. -/
theorem researchLeaves5_of_open7 (r : OpenResearchLeaves7) : OpenResearchLeaves5 where
  r1r2 := r.r1r2
  r1b := QMSplit.Moduli.r1b_of' r.shimuraFamily
  r1rec := r.r1rec
  r3 := r.r3
  r4 := QMSplit.Theta.thetaModularity_of r.igusaPsi4 r.igusaChi10
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r7a := r.r7a
  r7b := r.r7b
  r8 := r.r8
  r9a := r.r9a
  r9b := r.r9b
  r10 := r.r10
  r11r12 := r.r11r12
  r13 := r.r13
  r14 := HodgeLF7.r14Det (_root_.ZInQ.Contrib.HodgeSplit.r14Det_of_printed r.dsThm965 r.dsThm966)
  r15 := r.r15
  r16 := r.r16
  r17 := r.r17
  r18 := r.r18
  r19 := r.r19
  r20 := r.r20
  r21 := r.r21
  r22 := r.r22
  h5fin := r.h5fin

/-- leaf-fold6's textbook bundle from leaf-fold7's. -/
theorem textbookLeaves6_of_open7 (t : OpenTextbookLeaves7) (l : OpenAddedLeaves7) : OpenTextbookLeaves6 where
  t3Surj := t.t3Surj
  t4 := _root_.AvSplit.Final.h24 t.mulEtaleAbelianScheme
  t5 := _root_.AvSplit.Final.h25 t.mumfordTorsionAlgClosed
  homFreeFiniteAlgClosed := t.homFreeFiniteAlgClosed
  charPolyIndepOfEllAlgClosed := t.charPolyIndepOfEllAlgClosed
  t8 := _root_.AVGlue.poincareReducibility_of_published' t.cartierSmooth t.poincareComplement
    (isogenyQuasiInverseAG_lf7 l.milneIsogenyQuasiInverse) t.geomConnOfRationalPoint t.groupSchemeEquidim
  t10 := t.t10
  homLatticeCorr := _root_.AvSplit.Final.h69 t.uniformizationLeafAll t.gagaMorphism
  t11bExists := t.t11bExists
  t23 := HodgeLF7.t23 (_root_.ZInQ.Contrib.HodgeSplit.t23_all_of_bdrInvariants t.bdRInvariants)
  t24 := t.t24
  t27 := QMSplit.Yu.qmDichotomyYu_of_yu t.yuThm11
  t33 := t.t33
  dimJacobianEqGenus := t.dimJacobianEqGenus
  genusX1Field := t.genusX1Field
  t35 := _root_.AvSplit.Final.h38 t.uniformizationLeafAll t.mumfordTorsionAlgClosed
  normalModelOfFunctionFieldQ := t.normalModelOfFunctionFieldQ
  normalCurveSmoothQ := _root_.CurveSplit.normalCurveSmoothQ_of_regularSmooth t.regularSmoothPerfect
  geomConnectedOfConstantFieldQ :=
    _root_.CurveSplit.geomConnectedOfConstantFieldQ_of_zariski l.zariskiConnectedness
  x0Transitive := t.x0Transitive
  neronSchemeExtensionExists := t.neronSchemeExtensionExists

/-- The three QM rows from `QMCentralizerCMC` and T11(b) (qm-split's `rows_of_C`). -/
theorem qmRows_of7 (t : OpenTextbookLeaves7) (l : OpenAddedLeaves7) :
    HeckeRest.QMAutCard ∧ HeckeRest.ALFixedPoints ∧ FS5NoCM.CMOptimalEmbedding :=
  QMSplit.Aut.rows_of_C l.qmCentralizerCMC (t11b_of_exists5 t.t11bExists)

/-- leaf-fold6's added bundle from leaf-fold7's. -/
theorem addedLeaves6_of_open7 (t : OpenTextbookLeaves7) (l : OpenAddedLeaves7) : OpenAddedLeaves6 where
  cmOptimalEmbedding := (qmRows_of7 t l).2.2
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmHauptmodulBase3 := l.qmHauptmodulBase3
  qmClassNumberOne := QMSplit.CNO.qmClassNumberOne_proof
  senTwist := HodgeLF7.senTwist (_root_.ZInQ.Contrib.HodgeSplit.senTwist_of_tate l.tateTwistInvariants l.axSenTate)
  finiteImageHT :=
    HodgeLF7.finiteImageHT (_root_.ZInQ.Contrib.HodgeSplit.finiteImageHT_of_tate l.tateTwistInvariants l.axSenTate)
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  isogenyQuasiInverse := isogenyQuasiInverse_lf7 l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := (qmRows_of7 t l).1
  alFixedPoints := (qmRows_of7 t l).2.1
  zariskiConnectedness := l.zariskiConnectedness
  stQM := stQM_lf7 l.shimuraTaniyamaQbar
  valenceFormulaGammaStar := l.valenceFormulaGammaStar
  egaIV_8_8_2_ii := l.egaIV_8_8_2_ii
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := l.egaIV_17_7_8_ii
  shimuraGoodReduction := l.shimuraGoodReduction
  curveBijIso := curveBijIso_lf7

/-- leaf-fold6's glue bundle from leaf-fold7's. -/
theorem glue6_of_open7 (g : OpenGlue7) : OpenGlue6 where
  modelCoordinateResidue := MCRGlue.modelCoordinateResidue_of_quotient' g.quotientP1Coordinate

/-- **G0 with only the open leaves and the open glue** (leaf-fold7; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from `OpenResearchLeaves7` (28), `OpenTextbookLeaves7` (23), `OpenAddedLeaves7` (16)
and `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is `docs/research/leaf-fold7.md` §2. -/
theorem sixContactMin_of_open7 (r : OpenResearchLeaves7) (t : OpenTextbookLeaves7) (l : OpenAddedLeaves7)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open6 (researchLeaves5_of_open7 r) (textbookLeaves6_of_open7 t l) (addedLeaves6_of_open7 t l)
    (glue6_of_open7 g)

end HSyn

end HDec
