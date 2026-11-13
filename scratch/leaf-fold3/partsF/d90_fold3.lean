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

/-! ### The open statements -/

/-- **The textbook leaves still open** (leaf-fold3): `OpenTextbookLeaves2` with
* `t11a` (T11(a), `T11a_RiemannEnd`) replaced by hom-unify's single leaf `HomLatticeCorr`, which
  implies it and the added leaf `HomLinearLift` (part c30);
* `t40` (T40) replaced by `X0Transitive` (t40-tate, t40-igusa), which implies T40 and T39. -/
structure OpenTextbookLeaves3 : Prop where
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
(proved, part c10) and `homLinearLift` (from `HomLatticeCorr`, part c30). -/
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

/-- **The glue still open** (leaf-fold3): `OpenGlue2` without `hodgeBCInjective`,
`omegaBaseChange` (hodge-bc2), `cPtsTransport` (cpts-transport), `conjIsogMaps` (twist-descent)
and `modelG3` (linked-tate's route with lt-goodred's `GoodRedTorsion`). -/
structure OpenGlue3 : Prop where
  periodMapGlue : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  hauptmodulUnique : G0Split.FibreQM.HauptmodulUnique
  propTSAll : G0ModField.PropTSAll
  linkedTateLocal : G0AssembleMod.LinkedTateLocal

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
      (productMetrizationOfProductUnif_of_t35 t.t35)
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
      (G0ModField.fibreCoverExists_of_propTSAll' t.t5 g.propTSAll unramifiedConjugates_proved)
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
        (G0AssembleMod.linkedTateData_of_local t.t7 g.linkedTateLocal))
    heightCopies := G0HeightCopies.heightCopiesAgree }

/-- **G0 with only the open leaves and the open glue** (leaf-fold3; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from
* `OpenResearchLeaves2`: 26 research-level fields (unchanged from leaf-fold2);
* `OpenTextbookLeaves3`: 18 textbook fields (`HomLatticeCorr` for T11(a), `X0Transitive` for T40);
* `OpenAddedLeaves3`: 11 leaves (8 LEAF, 3 LEAF?);
* `OpenGlue3`: 4 glue Props.
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
#print axioms HSyn.t40_of_x0Transitive
#print axioms HSyn.t39_of_x0Transitive
#print axioms HomUnify.homLinearLift_of_corr
#print axioms HomUnify.t11a_riemannEnd_of_corr
#print axioms HSyn.textbookLeaves2_of_open3
#print axioms HSyn.gluePieces_of_open3
#print axioms HSyn.sixContactMin_of_open3
