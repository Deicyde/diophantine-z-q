import ZInQKernel.OneProof.H.TailH

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
    (hRay : PkgI2.RaynaudCriterionNF.{0}) (hTors : PkgI2.TorsionStructure.{0}) :
    G0AssembleMod.ModelG3G6 :=
  HSyn.LinkedTate.modelG3G6_of hFS (HSyn.LinkedTate.qmModelG3_of hNOS hRay hTors
    (HSyn.LinkedTate.goodRedG3Bridge_of_torsion goodRedTorsion_proved3))

/-- **`QMEndRank` from T6 and T27** (lt-goodred, part c75; not needed by the route below, since
`LinkedTateLocal` stays a glue field; recorded). -/
theorem qmEndRank_of_leaves3 (hM1 : PkgI3.HomFreeFinite) (hYu : QMLattice.YuB6Alg) :
    HSyn.LinkedTate.QMEndRank :=
  LTGoodRed.QM.qmEndRank_of_leaves hM1 hYu

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
-- (leaf-fold4) hecke-rest now proves ChartProper and ChartQuasiFinite; hP, hQ are unused here.
theorem propTSAll_of_pieces3 (hR : LeafAdopt.R1R2fpRepW) (h5 : PkgI2.TorsionStructure.{0})
    (hconn : TSHecke.Y3Connected) (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3)
    (hW : HeckeRest.ALFixedPoints) (hP : HeckeRestCurve.ChartProper)
    (hQ : HeckeRestCurve.ChartQuasiFinite) (hV : HeckeRestNV.HeckeVertWitness) :
    G0ModField.PropTSAll :=
  PropTSRed.propTSAll_of_bundle_meet t2_proved (LeafAdopt.R1R2fp_of_rep hR) KummerComp.kummerMeetGlue
    PropTSGlue.specNonMeeting (mobiusGlue_of_t5' h5)
    (HeckeRestAll.coverModelOfHecke_of_heckeRest hconn (LeafAdopt.R1R2fp_of_rep hR)
      (ObjBridge.torsionStructure_iff.mpr h5) hA hS hW hV)

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
theorem linkedTateLocal_of_leaves3 (hR6 : PkgI2.RaynaudCriterionNF.{0}) (h5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hN : PkgI2.NeronMappingAbelianScheme.{0}) (hFS : G0Split.FibreSimple)
    (h6 : PkgI3.HomFreeFinite) (hYu : QMLattice.YuB6Alg) : G0AssembleMod.LinkedTateLocal :=
  LTLocal.linkedTateLocal_of_tateBridge35 hR6
    (ObjBridge.torsionStructure_iff.mpr h5) (@UnramRootsTask.unramRoots_all 2 _ 5 _)
    (@UnramRootsTask.unramRoots_all 2 _ 3 _)
    (FrobPiecesGood.tateBridge35_of_neron_nmp hT hsp hc hRed hN) hFS (qmEndRank_of_leaves3 h6 hYu)

/-! ### The open statements -/

/-- **The textbook leaves still open** (leaf-fold3): `OpenTextbookLeaves2` with
* `t11a` (T11(a), `T11a_RiemannEnd`) replaced by hom-unify's single leaf `HomLatticeCorr`, which
  implies it and the added leaf `HomLinearLift` (part c30);
* `t40` (T40) kept: t40-tate and t40-igusa prove it from `X0Transitive`
  (`ZInQ.RLeaf.x1RationalCusp_of_x0Transitive`, `ZInQKernel/Contrib/RLeaf/T40.lean`), but that module
  imports Tau Ceti's `Backport` copy of `Units.val_mul_zpow_natCast_mul`, which clashes with the Tau Ceti
  modules this chain imports (T14 etc.), so it cannot be imported here; `X1RationalCusp` is over Mathlib
  definitions only, so the kernel theorem applies to this field verbatim outside this file;
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
  /-- hom-unify: the analytic representation `Hom(A, B) → {M : MΛ_A ⊆ Λ_B}` (lifting for every
  `K`, bijective over `ℂ`); Birkenhake–Lange §1.2, Mumford §1, §3, GAGA (UNVERIFIED numbers).
  Replaces T11(a) and `HomLinearLift`. -/
  homLatticeCorr : HomUnify.HomLatticeCorr
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  t24 : EigenformTwist
  t26 : PkgI3.TateModuleFree
  t33 : LeafModCurves.JacobianExists ℚ
  t35 : ZInQ.LeafPush2.UniformizationExists
  t38 : X1Belyi.CurveOfFunctionFieldQ
  /-- T40 (x1-belyi): `K_N` has a degree-one place (in the kernel: from `X0Transitive`). -/
  t40 : X1Belyi.X1RationalCusp
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
  periodMapGlue : ∀ h : LeafAdopt.R1R2fpRepW,
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
  t11a := HomUnify.t11a_riemannEnd_of_corr t.homLatticeCorr
  t11b := t.t11b
  t24 := t.t24
  t26 := t.t26
  t33 := t.t33
  t35 := t.t35
  t38 := t.t38
  t40 := t.t40
  t41 := t.t41

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
#print axioms HomUnify.homLinearLift_of_corr
#print axioms HomUnify.t11a_riemannEnd_of_corr
#print axioms HSyn.textbookLeaves2_of_open3

end G0A2_d90_fold3

end HDec
