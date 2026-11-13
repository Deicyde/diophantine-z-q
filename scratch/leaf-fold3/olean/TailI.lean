import TailH

namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

section G0A2_d90_fold3
/-! ## leaf-fold3: the results proved since leaf-fold2, folded into the statement of what remains open

Task leaf-fold3, 2026-11-13. Everything above this part is leaf-fold2's `Leaves2.lean` (with
g0-assemble3's `G7Data` bound `[L:ℚ] ≤ D`, `mk_g7bound.py`, and the fork's issue #2 items 2, 5, 8,
`mk_prefix.py`) and the parts `partsF/c*.lean` (`mk_lf3.py`). Each closed field is a theorem
`HSyn.xxx_proved3` whose type is this file's own Prop and whose proof is the copied or imported
theorem, so Lean checks that the statements agree. -/

noncomputable section

namespace HSyn

open CategoryTheory AlgebraicGeometry G0Split

/-! ### Fields closed since leaf-fold2 -/

/-- **`HodgeBCInjective` proved** (hodge-bc2; heightbc-contrib's `ZInQKernel/Contrib/HeightBC/`
holds the same proof over the kernel's objects; here part c60 over this file's). -/
theorem hodgeBCInjective_proved3 : ZInQ.HeightBC.HodgeBCInjective := ZInQ.HeightBC.hodgeBCInjective

/-- **`OmegaBaseChange` proved** (hodge-bc2, part c60). -/
theorem omegaBaseChange_proved3 : ZInQ.HeightBC.OmegaBaseChange := ZInQ.HeightBC.omegaBaseChange

/-- **`CPtsTransport` proved** (cpts-transport, part c20; rigidity from mul-rigidity). -/
theorem cPtsTransport_proved3 : G0Split.FibreQM.CPtsTransport :=
  G0Split.FibreQM.cPtsTransport_proof

/-- **`ConjIsogMaps` proved** (twist-descent's `conjIsogMaps_of_mulIsogeny`, part c50, over kf-glue,
part c40, with `MulIsogeny` proved by g9-abvarbc, `mulIsogeny_proved`: the same Prop
`G0FibreSimple.MulIsogeny`). -/
theorem conjIsogMaps_proved3 : G0ModField.KernelField.ConjIsogMaps :=
  G0ModField.KernelField.conjIsogMaps_of_mulIsogeny mulIsogeny_proved

/-- **`BurnsideAbsIrred` proved** (rv-gluepieces2, part c10: Schur + Jacobson density). -/
theorem burnsideAbsIrred_proved3 : G0Galois.BurnsideAbsIrred := RvGP2.burnsideAbsIrred

/-- **`GoodRedTorsion` proved** (lt-goodred, part c75). -/
theorem goodRedTorsion_proved3 : HSyn.LinkedTate.GoodRedTorsion := LTGoodRed.goodRedTorsion

/-- **G3 and G5-G6 on G7's model from the leaves R6, R7a, T5** (linked-tate's route, part c70,
with `GoodRedTorsion` proved and `FibreSimple`): replaces g0-assemble2's glue `ModelG3`. -/
theorem modelG3G6_of_leaves3 (hFS : G0Split.FibreSimple) (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : PkgI2.RaynaudCriterion.{0}) (hTors : PkgI2.TorsionStructure.{0}) :
    G0AssembleMod.ModelG3G6 :=
  HSyn.LinkedTate.modelG3G6_of hFS (HSyn.LinkedTate.qmModelG3_of hNOS hRay hTors
    (HSyn.LinkedTate.goodRedG3Bridge_of_torsion goodRedTorsion_proved3))

/-- **`QMEndRank` from T6 and T27** (lt-goodred, part c75; not needed by the route below, since
`LinkedTateLocal` stays a glue field; recorded). -/
theorem qmEndRank_of_leaves3 (hM1 : PkgI3.HomFreeFinite) (hT27 : PkgI3.QMDichotomyYu) :
    HSyn.LinkedTate.QMEndRank :=
  LTGoodRed.QM.qmEndRank_of_leaves hM1 hT27

/-- **T40 from `X0Transitive`** (t40-tate, t40-igusa: `ZInQKernel/Contrib/RLeaf/T40.lean`, imported;
`X1Belyi.X1RationalCusp` is over Mathlib definitions only, so the kernel theorem has this file's
type). -/
theorem t40_of_x0Transitive (h : _root_.ZInQ.RLeaf.X0Transitive) : X1Belyi.X1RationalCusp :=
  _root_.ZInQ.RLeaf.x1RationalCusp_of_x0Transitive h

/-- **T39 from `X0Transitive`** (same module). -/
theorem t39_of_x0Transitive (h : _root_.ZInQ.RLeaf.X0Transitive) : X1Belyi.X1ConstantField :=
  _root_.ZInQ.RLeaf.x1ConstantField_of_x0Transitive h

/-- **`TangentDimAtOrigin` from the kernel's Contrib** (dim-contrib, `ZInQ.Contrib.Dim.tangentDimAtOrigin`,
`ZInQKernel/Contrib/Dim/HodgeLattice.lean`, imported; through leaf-fold2's field map `toAbVarK`). It replaces
leaf-fold2's use of the scratch copy `LF2SmoothDim` in the product-metrization step below. -/
theorem tangentDimAtOrigin_proved3 : ZInQ.DefFaltings.HodgeLattice.TangentDimAtOrigin :=
  fun L _ B g hg => _root_.ZInQ.Contrib.Dim.tangentDimAtOrigin L (toAbVarK B) g hg

/-- **Proposition TS for every admissible cover** (prop-ts, prop-ts-glue 3d41b3d5, ts-kummer, kummer-comp,
ts-hecke, hecke-rest; part c80): prop-ts's `propTSAll_of_bundle_meet` with `KummerMeetGlue` proved
(kummer-comp), `SpecNonMeeting` proved (prop-ts-glue), T2 proved (leaf-fold), `MobiusGlue` from T5
(image-plane), and `CoverModelOfHecke` from hecke-rest's eight inputs: the leaf candidates `Y3Connected`
(R1conn), `QMAutCard`, `SerreRigidity3`, `ALFixedPoints`, the leaf T5, and the glue `ChartProper`,
`ChartQuasiFinite`, `HeckeVertWitness`. -/
theorem propTSAll_of_pieces3 (hR : LeafAdopt.R1R2fpRep) (h5 : PkgI2.TorsionStructure.{0})
    (hconn : TSHecke.Y3Connected) (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3)
    (hW : HeckeRest.ALFixedPoints) (hP : HeckeRestCurve.ChartProper)
    (hQ : HeckeRestCurve.ChartQuasiFinite) (hV : HeckeRestNV.HeckeVertWitness) :
    G0ModField.PropTSAll :=
  PropTSRed.propTSAll_of_bundle_meet t2_proved (LeafAdopt.R1R2fp_of_rep hR) KummerComp.kummerMeetGlue
    PropTSGlue.specNonMeeting (mobiusGlue_of_t5' h5)
    (HeckeRestAll.coverModelOfHecke_of_heckeRest hconn (LeafAdopt.R1R2fp_of_rep hR)
      (ObjBridge.torsionStructure_iff.mpr h5) hA hS hW hP hQ hV)

/-- **`LinkedTateLocal` (g0-assemble2's GLUE field 39) from leaves and one glue Prop** (lt-local's
`linkedTateLocal_of_tateBridge35` over the `G7Data` with `[L:ℚ] ≤ D`; part c85). Its inputs:
* R6 (`RaynaudCriterion`), T5 (`TorsionStructure`, I2-Tors), T26 (I3.M0, `TateModuleFree`);
* `UnramRoots 2 5`, `UnramRoots 2 3`: proved (unram-roots, Tau Ceti);
* `TateBridge35` (g14-trace's data, ε = 1 on `G_L × G_L` from the descent datum, lt-local's
  `g7Clauses_of_transport`): from frob-pieces' `tateBridge35_of_neron_nmp`, i.e. T26, neron-lg's glue
  N1-g1 `AbVarSpreadsOut`, the leaf candidate `ProperSmoothGenConnected` (Zariski's connectedness
  theorem) and the textbook leaves I2-Red (`ReductionTorsionBijective`) and I2-NMP
  (`NeronMappingAbelianScheme`); `AbsFrob`, `SmoothGeomConnIntegral`, `FExtendGen` are proved there;
* `FibreSimple` (derived below) and `QMEndRank` (lt-goodred, from T6 and T27).
lg-kerwild's every-`ℓ` theorem `exists_localGlue_of_tateModuleFree` (rv-fast's CONCERN) is not used. -/
theorem linkedTateLocal_of_leaves3 (hR6 : PkgI2.RaynaudCriterion.{0}) (h5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hN : PkgI2.NeronMappingAbelianScheme.{0}) (hFS : G0Split.FibreSimple)
    (h6 : PkgI3.HomFreeFinite) (h27 : PkgI3.QMDichotomyYu) : G0AssembleMod.LinkedTateLocal :=
  LTLocal.linkedTateLocal_of_tateBridge35 (ObjBridge.raynaudCriterion_iff.mpr hR6)
    (ObjBridge.torsionStructure_iff.mpr h5) (@UnramRootsTask.unramRoots_all 2 _ 5 _)
    (@UnramRootsTask.unramRoots_all 2 _ 3 _)
    (FrobPiecesGood.tateBridge35_of_neron_nmp hT hsp hc hRed hN) hFS (qmEndRank_of_leaves3 h6 h27)

/-! ### The open statements -/

/-- **The textbook leaves still open** (leaf-fold3): `OpenTextbookLeaves2` with
* `t11a` (T11(a), `T11a_RiemannEnd`) replaced by hom-unify's single leaf `HomLatticeCorr`, which
  implies it and the added leaf `HomLinearLift` (part c30);
* `t40` (T40) replaced by `X0Transitive` (t40-tate, t40-igusa), which implies T40 and T39;
* `t3` (I2-NMP) and `t4` (I2-Red) back (leaf-fold2 had deleted them as unused): lt-local's route to
  `LinkedTateLocal` uses them through frob-pieces. -/
structure OpenTextbookLeaves3 : Prop where
  /-- T3 = I2-NMP: Néron mapping property of abelian schemes over a DVR (BLR §1.2 Prop. 8,
  UNVERIFIED locator; kernel `PkgI2.NeronMappingAbelianScheme`). -/
  t3 : PkgI2.NeronMappingAbelianScheme.{0}
  /-- T4 = I2-Red: reduction is bijective on prime-to-`p` torsion for good reduction (kernel
  `PkgI2.ReductionTorsionBijective`). -/
  t4 : PkgI2.ReductionTorsionBijective.{0}
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : LeafPush.T09_WeilPairing.{0}
  t10 : T10Etale.T10_TateDuality
  /-- hom-unify: the analytic representation `Hom(A, B) → {M : MΛ_A ⊆ Λ_B}` (lifting for every
  `K`, bijective over `ℂ`); Birkenhake–Lange §1.2, Mumford §1, §3, GAGA (UNVERIFIED numbers).
  Replaces T11(a) and `HomLinearLift`. -/
  homLatticeCorr : HomUnify.HomLatticeCorr
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomyYu
  t33 : LeafModCurves.JacobianExists ℚ
  t34 : LeafModCurves.DimJ1Genus
  t35 : ZInQ.LeafPush2.UniformizationExists
  t38 : X1Belyi.CurveOfFunctionFieldQ
  /-- t40-igusa: Galois acts transitively on the cyclic subgroups of order `N` of the generic
  elliptic curve `E_j` over `ℚ(j)` (irreducibility of `X₀(N)` over `ℚ(j)`). Replaces T40. -/
  x0Transitive : _root_.ZInQ.RLeaf.X0Transitive
  t41 : ZInQ.H5Neron.NeronModelExists

/-- **The added leaves still open** (leaf-fold3): `OpenAddedLeaves2` without `burnsideAbsIrred`
(proved, part c10) and `homLinearLift` (from `HomLatticeCorr`, part c30), with the four leaves under
Proposition TS (ts-hecke, hecke-rest). -/
structure OpenAddedLeaves3 : Prop where
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmHauptmodul : PkgI1.QMHauptmodul
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  qmDenZeroCM3 : G0Split.FibreQM.QMDenZeroCM3
  senTwist : G0Galois.SenTwist
  finiteImageHT : G0Galois.FiniteImageHT
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  divisiblePoints : WeilPairing.DivisiblePoints
  x6ConicModel : X6Kummer.X6ConicModel
  /-- ts-hecke, LEAF? (R1conn: `Y₃` is connected over `ℚ`, on one witness of R1fp; Shimura, Deligne
  Bourbaki 389 §§2-3; the component count is computed in `scratch/ts-hecke/pi0_check.py`). -/
  y3Connected : TSHecke.Y3Connected
  /-- hecke-rest, LEAF (automorphism groups of QM abelian surfaces: 4, 6 or 2; Shimura's
  classification of `End⁰`, units of quadratic orders). -/
  qmAutCard : HeckeRest.QMAutCard
  /-- hecke-rest, LEAF (Serre's lemma: a finite-order endomorphism fixing `A[3]` is `1`). -/
  serreRigidity3 : HeckeRest.SerreRigidity3
  /-- hecke-rest, LEAF (fixed points of the Atkin–Lehner involutions on `X₀⁶(1)`: Ogg 1983,
  Rotger 2004). -/
  alFixedPoints : HeckeRest.ALFixedPoints
  /-- frob-pieces, LEAF? (Zariski's connectedness theorem for a smooth proper scheme over
  `𝓞_L[1/f]` with geometrically connected generic fibre; EGA III₁ 4.3, UNVERIFIED). -/
  properSmoothGenConnected : FrobPiecesNeron.ProperSmoothGenConnected

/-- **The glue still open** (leaf-fold3): `OpenGlue2` without `hodgeBCInjective`,
`omegaBaseChange` (hodge-bc2), `cPtsTransport` (cpts-transport), `conjIsogMaps` (twist-descent)
and `modelG3` (linked-tate's route with lt-goodred's `GoodRedTorsion`), with `propTSAll` replaced by
the three glue Props hecke-rest leaves under it (`propTSAll_of_pieces3`), and with `linkedTateLocal`
replaced by N1-g1 `AbVarSpreadsOut` (`linkedTateLocal_of_leaves3`). -/
structure OpenGlue3 : Prop where
  periodMapGlue : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  hauptmodulUnique : G0Split.FibreQM.HauptmodulUnique
  /-- hecke-rest: the charts of `π : Y₃ → P¹` are proper (curve theory). -/
  chartProper : HeckeRestCurve.ChartProper
  /-- hecke-rest: the charts of `π` are quasi-finite (curve theory). -/
  chartQuasiFinite : HeckeRestCurve.ChartQuasiFinite
  /-- hecke-rest: one vertical prime above `p > 324` unramified in the Hecke cover (equivalent to
  Lemma NV, `HeckeNoVertRam`). -/
  heckeVertWitness : HeckeRestNV.HeckeVertWitness
  /-- neron-lg's N1-g1: an abelian variety over a number field spreads out to an abelian scheme
  over `𝓞_L[1/f]` (EGA IV₃ 8.8.2, 8.10.5, IV₄ 17.7.8; textbook, not in Mathlib). Replaces
  `LinkedTateLocal` through lt-local's route (`linkedTateLocal_of_leaves3`). -/
  abVarSpreadsOut : FrobPiecesNeron.AbVarSpreadsOut

/-! ### Back to leaf-fold2's bundles -/

theorem textbookLeaves2_of_open3 (t : OpenTextbookLeaves3) : OpenTextbookLeaves2 where
  t5 := t.t5
  t6 := t.t6
  t7 := t.t7
  t8 := t.t8
  t9 := t.t9
  t10 := t.t10
  t11a := HomUnify.t11a_riemannEnd_of_corr t.homLatticeCorr
  t11b := t.t11b
  t23 := t.t23
  t24 := t.t24
  t26 := t.t26
  t27 := t.t27
  t33 := t.t33
  t34 := t.t34
  t35 := t.t35
  t38 := t.t38
  t40 := t40_of_x0Transitive t.x0Transitive
  t41 := t.t41

/-- **Leaves.lean's `GluePieces` from the open statements** (leaf-fold2's `gluePieces_of_open2`
with the five closed glue fields replaced by their proofs, G3-G6 from linked-tate's route, and
Burnside and `HomLinearLift` from parts c10, c30). -/
theorem gluePieces_of_open3 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves3)
    (l : OpenAddedLeaves3) (g : OpenGlue3) : GluePieces :=
  let t2 := textbookLeaves2_of_open3 t
  let r3 := researchLeaves3_of_open2 r
  let t3 := textbookLeaves_of_open2 t2
  have hMob : LeafQM.AV.Pin.MobiusGlue := mobiusGlue_of_t5' t.t5
  have hFS5 : G0FibreSimple.FibreComTrivial :=
    fibreComTrivial_of_full (FS5NoCM.fibreComTrivialFull_of_leaves'' (r1r2fpFull_of r3)
      hMob t.t27 t.t6 l.cmOptimalEmbedding (X6Kummer.x6KummerFibre_of_conic hMob l.x6ConicModel)
      r.r5count)
  have hFS : G0Split.FibreSimple :=
    G0FibreSimple.fibreSimple_of_leaves t3 mulIsogeny_proved G0FibreSimple.rigidityHom
      ⟨G0FibreSimple.finiteDescends_proof, hFS5⟩
  { dimFinite := G0Split.dimFinite
    dimBaseChange := G0Split.dimBaseChange
    fibreSimple := hFS
    productModelHeight := ZInQ.ProductHeight.productModelHeight_of_splits productUnifSplits_proved
      (ZInQ.UnifDims.productMetrizationOfProductUnif_of_tangentDim t.t35 tangentDimAtOrigin_proved3)
    stableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine
      (ZInQ.HeightBC.g0_hodgeLine_iff.mpr (ZInQ.HeightBC.hodgeLineBaseChange_of_glue4
        hodgeBCInjective_proved3 cotangentSpanBC_proved omegaBaseChange_proved3
        uniformizationLiftAnalytic_proved))
    productExists := G0Product.productExists
    reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3 r3 G0Split.dimFinite
    thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios
      (G0Split.FibreQM.fibreQMPeriod_main_rep r.r1r2 hMob l.qmHauptmodul
        t.t35 t2.t11a l.qmClassNumberOne (r.r1b r.r1r2) (g.periodMapGlue r.r1r2)
        g.hauptmodulUnique l.qmDenZeroCM3 cPtsTransport_proved3)
      l.thetaRatiosAlgebraic
    modularConstituent := modularConstituent_of_field t3
      (G0ModField.fibreCoverExists_of_propTSAll' t.t5
        (propTSAll_of_pieces3 r.r1r2 t.t5 l.y3Connected l.qmAutCard l.serreRigidity3 l.alFixedPoints
          g.chartProper g.chartQuasiFinite g.heckeVertWitness) unramifiedConjugates_proved)
      (G0ModField.KernelField.kernelFieldExists_of_split'' t.t6 r.r7a r.r6 t.t5 t.t27
        hFS5 G0ModField.KernelField.oMaximal endTransport_proved conjIsogMaps_proved3)
      UnramTate.unramifiedSup_mf
      (G0AssembleMod.afterG7_of3 r3 t3
        ⟨burnsideAbsIrred_proved3, r.r14,
          g9Glue_of_deRhamComparisonHT r.r10,
          G0Galois.g10Glue_of_conjTwist
            (G0Galois.conjTwistNontrivial_of_leaves t.t5 t.t26 t.t35
              (HomUnify.homLinearLift_of_corr t.homLatticeCorr)),
          G0Galois.g12Weight_of_senTwist l.senTwist l.finiteImageHT,
          G0Galois.detTate_of_leaves l.t09SymmIsogenyExists l.isogenyQuasiInverse
            l.divisiblePoints t.t26,
          G0AssembleMod.resQFiniteIndex⟩
        (G0ModNewform.dirichletOfFinite_of_t17 t17_proved) r.r17
        Swan.swanIndependent_proved Swan.swanIntegral_proved
        Swan.adaptedExists_proved
        (modelG3G6_of_leaves3 hFS r.r7a r.r6 t.t5)
        (G0AssembleMod.linkedTateData_of_local t.t7
          (linkedTateLocal_of_leaves3 r.r6 t.t5 t.t26 g.abVarSpreadsOut l.properSmoothGenConnected
            t.t4 t.t3 hFS t.t6 t.t27)))
    heightCopies := G0HeightCopies.heightCopiesAgree }

/-- **G0 with only the open leaves and the open glue** (leaf-fold3; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from
* `OpenResearchLeaves2`: 26 research-level fields (unchanged from leaf-fold2);
* `OpenTextbookLeaves3`: 20 textbook fields (`HomLatticeCorr` for T11(a), `X0Transitive` for T40,
  T3 and T4 back);
* `OpenAddedLeaves3`: 16 leaves (11 LEAF, 5 LEAF?);
* `OpenGlue3`: 6 glue Props.
The table of every field is `docs/research/leaf-fold3.md` §2. -/
theorem sixContactMin_of_open3 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves3)
    (l : OpenAddedLeaves3) (g : OpenGlue3) : ZInQ.SixContactMin :=
  sixContactMin_of_leavesR3 (researchLeaves3_of_open2 r)
    (textbookLeaves_of_open2 (textbookLeaves2_of_open3 t)) (gluePieces_of_open3 r t l g)

end HSyn

end

#print axioms HSyn.hodgeBCInjective_proved3
#print axioms HSyn.omegaBaseChange_proved3
#print axioms HSyn.cPtsTransport_proved3
#print axioms HSyn.conjIsogMaps_proved3
#print axioms HSyn.burnsideAbsIrred_proved3
#print axioms HSyn.goodRedTorsion_proved3
#print axioms HSyn.modelG3G6_of_leaves3
#print axioms HSyn.qmEndRank_of_leaves3
#print axioms HSyn.tangentDimAtOrigin_proved3
#print axioms HSyn.propTSAll_of_pieces3
#print axioms HSyn.linkedTateLocal_of_leaves3
#print axioms HSyn.t40_of_x0Transitive
#print axioms HSyn.t39_of_x0Transitive
#print axioms HomUnify.homLinearLift_of_corr
#print axioms HomUnify.t11a_riemannEnd_of_corr
#print axioms HSyn.textbookLeaves2_of_open3
#print axioms HSyn.gluePieces_of_open3
#print axioms HSyn.sixContactMin_of_open3

end G0A2_d90_fold3

end HDec
