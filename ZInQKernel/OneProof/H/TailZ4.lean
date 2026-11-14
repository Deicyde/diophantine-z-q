import ZInQKernel.OneProof.H.TailX
import ZInQKernel.OneProof.H.TailZ
import ZInQKernel.OneProof.H.TailZ3
import ZInQKernel.Contrib.CloudW01Spread.FinitePresentation
import ZInQKernel.Contrib.CloudW01Spread.Smooth
import ZInQKernel.Contrib.CloudW02Connectedness.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.Main
import ZInQKernel.Contrib.CloudW06PoincareRigidity.T11bExists
import ZInQKernel.Contrib.CloudW08EigenformTwists.EigenformTwist

/-! # OneProof H, leaf-fold8: the next bundle generation

`HDec.HSyn.sixContactMin_of_open8 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8) (l : OpenAddedLeaves8)
(g : OpenGlue7)` proves `ZInQ.SixContactMin` by filling leaf-fold7's bundles (`sixContactMin_of_open7`, `TailX`)
from the new ones. Folded (docs/research/leaf-fold8.md lists every field):

* height-split + height-glue (`TailY`, `TailZ`): the research fields `r18`, `r19`, `r20`, `r21`, `r22`, `h5fin`
  from height-split's published-form leaves over the published stable height (`IsStableFaltingsHeight`): SS1-SS3,
  Bost, Javanpeykar, Faltings' Lemma 5, Pazuki, Gaudron–Rémond; N1 from the textbook field
  `neronSchemeExtensionExists`, and height-split's glue bundle `HeightGlue` from T35, which is a theorem from the
  textbook fields `uniformizationLeafAll`, `mumfordTorsionAlgClosed` (av-split);
* qm-glue (`TailZ2`, `TailZ3`): the added fields `valenceFormulaGammaStar` (H-87) and `qmHauptmodulBase3` (H-88)
  from the valence formula, Shimizu's covolume of `𝒪¹` and Lin–Yang's CM value at discriminant `−24` (with Igusa's
  two modularity statements, already fields);
* six cloud-worker Contrib theorems, each proving a field's Prop outright: `t3Surj`
  (`NeronMappingAbelianSchemeSurj_proof`), `t11bExists` (`T11bExists_proof`), `t24` (`EigenformTwist_proof`),
  `zariskiConnectedness` (`ZariskiConnectedness_proof`), `egaIV_8_8_2_ii`, `egaIV_17_7_8_ii`
  (`EGAIV_8_8_2_ii_proof`, `EGAIV_17_7_8_ii_proof`).

No existing module is edited; every field that is not folded keeps leaf-fold7's type. -/

namespace HDec

set_option maxHeartbeats 1000000

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ## Transports between the kernel's rows and the chain's copies -/

/-- The kernel's `R18_Javanpeykar` (proved by height-split) gives the chain's copy: the chain's
`ZInQ.LeafPush2.stableFaltingsHeight` (leaf-push2's copy of the Arakelov layer) is the kernel's by the proved
`G0HeightCopies.heightCopiesAgree`, and the curve and Jacobian predicates are converted field by field (as in
`r18Concrete_of`, in the other direction). -/
theorem r18_lf8 (h : _root_.ZInQ.LeafPush2.R18_Javanpeykar) : ZInQ.LeafPush2.R18_Javanpeykar := by
  intro K _ _ X hX _ P₀ J aj hJac g hg hg1 t ht d hd hd0
  have : _root_.LeafModCurves.IsCurve X := ⟨hX.proper, hX.smooth, hX.geomConnected⟩
  rw [G0HeightCopies.heightCopiesAgree K J]
  exact h K X P₀ J aj ⟨hJac.base, hJac.univ⟩ g hg hg1 t ht d hd hd0

/-- The kernel's `R22_Pazuki` (proved by height-split) gives the chain's copy (`heightCopiesAgree`). -/
theorem r22_lf8 (h : _root_.ZInQ.LeafPush2.R22_Pazuki) : ZInQ.LeafPush2.R22_Pazuki := by
  intro K _ _ A hA x hx
  rw [G0HeightCopies.heightCopiesAgree K A] at hx
  exact h K A hA x hx

/-- cloud-worker W06's `T11bExists` (proved) is the chain's `AVB2.T11bExists` (same text over the kernel's
`PkgI3.AbVar`). -/
theorem t11bExists_lf8 : AVB2.T11bExists := _root_.ZInQ.Contrib.CloudW06PoincareRigidity.T11bExists_proof

/-! ## The bundles -/

/-- **The research leaves still open** (leaf-fold8): leaf-fold7's `OpenResearchLeaves7` with the six height rows
`r18`-`r22`, `h5fin` replaced by height-split's leaves over the published stable height. 31 fields. -/
structure OpenResearchLeaves8 : Prop where
  r1r2 : LeafAdopt.R1R2fpRep
  shimuraFamily : QMSplit.Moduli.ShimuraFamily
  r1rec : LeafQM.AV.R1rec
  r3 : _root_.ZInQ.LeafPush2.R03_LinYang
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r5 : LeafQM.AV.R5fp
  r5count : LeafQM.AV.R5fpCount
  r6 : _root_.PkgI2.RaynaudCriterion.{0}
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r7b : _root_.PkgI2.SerreTatePotentialGood.{0}
  r8 : _root_.PkgI2.GrothendieckMonodromy.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r15 : DeligneSerreConseq
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, SS1: Grothendieck's semistable reduction theorem, global form (SGA 7 IX 3.6). -/
  semistableReductionThm : _root_.ZInQ.HeightSplit.SemistableReductionThm
  /-- height-split, SS2: base change of the identity component in the semistable case (SGA 7 IX 3.3). -/
  semistableNeronBaseChange : _root_.ZInQ.HeightSplit.SemistableNeronBaseChange
  /-- height-split, SS3: semistability persists under finite extension (SGA 7 IX 3.3). -/
  semistablePersists : _root_.ZInQ.HeightSplit.SemistablePersists
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.BostLowerBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-16: Faltings 1983 Lemma 5 (semistable form) over every number field `L ⊇ K`, replaces
  `r20`. -/
  faltingsLemma5BC : _root_.ZInQ.HeightSplit.FaltingsLemma5BC
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14

/-- **The textbook leaves still open** (leaf-fold8): leaf-fold7's `OpenTextbookLeaves7` without `t3Surj`,
`t11bExists` and `t24` (proved by cloud workers W03, W06, W08). 20 fields. -/
structure OpenTextbookLeaves8 : Prop where
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
  t33 : _root_.LeafModCurves.JacobianExists ℚ
  dimJacobianEqGenus : _root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus
  genusX1Field : _root_.ZInQ.Contrib.CurvesG.GenusX1Field
  normalModelOfFunctionFieldQ : _root_.ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ
  regularSmoothPerfect : _root_.CurveSplit.RegularSmoothPerfect
  igusaGL2 : _root_.ZInQ.RLeaf.IgusaGL2
  neronSchemeExtensionExists : _root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists

/-- **The added leaves still open** (leaf-fold8): leaf-fold7's `OpenAddedLeaves7` without `zariskiConnectedness`,
`egaIV_8_8_2_ii`, `egaIV_17_7_8_ii` (proved by cloud workers W02, W01), and with `valenceFormulaGammaStar`,
`qmHauptmodulBase3` replaced by the valence formula, Shimizu's covolume and the CM value at `−24` (qm-glue). 14
fields. -/
structure OpenAddedLeaves8 : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  x6ConicModel : X6Kummer.X6ConicModel
  y3Connected : TSHecke.Y3Connected
  shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  shimuraGoodReductionNoGuard : CurveSplitGR.ShimuraGoodReductionNoGuard
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop. 2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- qm-split, H-87/H-88: `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` (Shimura 1971 Prop. 9.2;
  Shimizu 1965). -/
  shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1
  /-- qm-glue, H-88: Lin–Yang's Igusa vector at the Baba–Granath CM value `j = −16/27` (discriminant `−24`). -/
  igusaCMValue24 : LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24

/-! ## From the new bundles to leaf-fold7's -/

/-- Height-split's leaf bundle from the new research fields and N1 (from `neronSchemeExtensionExists`). -/
theorem heightLeaves_of8 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8) :
    _root_.ZInQ.HeightSplit.HeightLeaves where
  n1 := _root_.ZInQ.Contrib.NeronC.neronModelExists_of_extension t.neronSchemeExtensionExists
  ss1 := r.semistableReductionThm
  ss2 := r.semistableNeronBaseChange
  ss3 := r.semistablePersists
  bost := r.bostLowerBound
  javanpeykar := r.javanpeykarBound
  faltings5 := r.faltingsLemma5BC
  pazuki := r.pazukiCor13Upper
  gaudronRemond := r.gaudronRemondThm14

/-- The six height rows from height-split's leaves and T35 (av-split's `h38` from the textbook fields). -/
theorem heightRows_of8 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8) :
    _root_.ZInQ.LeafPush2.R18_Javanpeykar ∧ _root_.ZInQ.DefFaltings.R19_GaudronRemond ∧
      _root_.ZInQ.DefFaltings.R20_FaltingsLemma5 ∧ _root_.ZInQ.DefFaltings.R21_Bost ∧
      _root_.ZInQ.LeafPush2.R22_Pazuki ∧ _root_.ZInQ.DefFaltings.StableHeightFinite :=
  _root_.ZInQ.HeightGlue.heightRows_of_t35 (heightLeaves_of8 r t)
    (_root_.AvSplit.Final.h38 t.uniformizationLeafAll t.mumfordTorsionAlgClosed)

/-- leaf-fold7's research bundle from leaf-fold8's. -/
theorem researchLeaves7_of_open8 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8) : OpenResearchLeaves7 where
  r1r2 := r.r1r2
  shimuraFamily := r.shimuraFamily
  r1rec := r.r1rec
  r3 := r.r3
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r7a := r.r7a
  r7b := r.r7b
  r8 := r.r8
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  dsThm965 := r.dsThm965
  dsThm966 := r.dsThm966
  r15 := r.r15
  r16 := r.r16
  r17 := r.r17
  r18 := r18_lf8 (heightRows_of8 r t).1
  r19 := (heightRows_of8 r t).2.1
  r20 := (heightRows_of8 r t).2.2.1
  r21 := (heightRows_of8 r t).2.2.2.1
  r22 := r22_lf8 (heightRows_of8 r t).2.2.2.2.1
  h5fin := (heightRows_of8 r t).2.2.2.2.2

/-- leaf-fold7's textbook bundle from leaf-fold8's. -/
theorem textbookLeaves7_of_open8 (t : OpenTextbookLeaves8) : OpenTextbookLeaves7 where
  t3Surj := _root_.ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj_proof.{0}
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
  t11bExists := t11bExists_lf8
  bdRInvariants := t.bdRInvariants
  t24 := _root_.ZInQ.Contrib.CloudW08EigenformTwists.EigenformTwist_proof
  yuThm11 := t.yuThm11
  t33 := t.t33
  dimJacobianEqGenus := t.dimJacobianEqGenus
  genusX1Field := t.genusX1Field
  normalModelOfFunctionFieldQ := t.normalModelOfFunctionFieldQ
  regularSmoothPerfect := t.regularSmoothPerfect
  igusaGL2 := t.igusaGL2
  neronSchemeExtensionExists := t.neronSchemeExtensionExists

/-- leaf-fold7's added bundle from leaf-fold8's. -/
theorem addedLeaves7_of_open8 (r : OpenResearchLeaves8) (l : OpenAddedLeaves8) : OpenAddedLeaves7 where
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmHauptmodulBase3 := LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of_leaves
    (QMSplit.Theta.thetaModularity_of r.igusaPsi4 r.igusaChi10) l.valenceFormulaCocompactEq l.shimizuCovolumeO1
    l.igusaCMValue24
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  zariskiConnectedness := _root_.ZariskiConn.ZariskiConnectedness_proof.{0}
  shimuraTaniyamaQbar := l.shimuraTaniyamaQbar
  valenceFormulaGammaStar :=
    LeafQCheck.HM.QMSplit.valenceFormulaGammaStar_of_leaves l.valenceFormulaCocompactEq l.shimizuCovolumeO1
  egaIV_8_8_2_ii := _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii_proof
  shimuraGoodReductionNoGuard := l.shimuraGoodReductionNoGuard

/-- **G0 with only the open leaves and the open glue** (leaf-fold8; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from `OpenResearchLeaves8` (31), `OpenTextbookLeaves8` (20), `OpenAddedLeaves8` (14)
and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is
`docs/research/leaf-fold8.md` §2. -/
theorem sixContactMin_of_open8 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8) (l : OpenAddedLeaves8)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open7 (researchLeaves7_of_open8 r t) (textbookLeaves7_of_open8 t) (addedLeaves7_of_open8 r l) g

end HSyn

end HDec
