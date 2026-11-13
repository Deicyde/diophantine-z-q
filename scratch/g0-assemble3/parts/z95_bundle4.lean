/-! ## g0-assemble3: `ResearchLeaves4`, `GluePieces4`, `sixContactMin_of_leaves4`

Task g0-assemble3, 2026-11-13. g0-assemble2's `GluePieces3` (part z90, 40 fields) with every later result applied
(parts b10-e30, z92). Each field of `GluePieces4` is a named `def … : Prop` of its source task, copied verbatim in that
task's part; kinds and sources are in `docs/research/g0-assemble3.md` §2 (LEAF = published theorem, LEAF? = leaf
candidate, GLUE = to be proved by the project). `ResearchLeaves4` is `ResearchLeaves3` with r10-amend's amended R10
(`DeRhamComparisonHT` = old R10 + the Hodge–Tate vanishing clause, which was `GluePieces3.g9R10Weights`). -/

noncomputable section

namespace HSyn

open G0Split

/-- **The research leaves after g0-assemble3**: `ResearchLeaves3` (part z80) with `r10` amended (r10-amend). -/
structure ResearchLeaves4 : Prop where
  r1r2 : LeafAdopt.R1R2fpRep
  r1rec : LeafQM.AV.R1rec
  r3 : ZInQ.LeafPush2.R03_LinYang
  r4 : PkgI1.ThetaModularity
  r5 : LeafQM.AV.R5fp
  r5count : LeafQM.AV.R5fpCount
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
  r8 : PkgI2.GrothendieckMonodromy.{0}
  r9a : PkgI3.FaltingsSemisimple
  r9b : PkgI3.FaltingsTate
  /-- R10 amended (r10-amend, `ZInQKernel/Contrib/R10/Amend.lean`): the de Rham comparison with the full
  Hodge–Tate weight multiset (Faltings 1988; Fontaine 1982; Tate 1967 §3.3; locators UNVERIFIED);
  `deRhamComparisonHT_iff : DeRhamComparisonHT ↔ PkgI4.DeRhamComparison ∧ G9Bridge.R10Weights`. -/
  r10 : ZInQ.Contrib.R10.DeRhamComparisonHT
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  r14 : EigenformRepExists
  r15 : DeligneSerreConseq
  r16 : LeafModCurves.R16_EichlerShimuraJ1'
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r20 : ZInQ.DefFaltings.R20_FaltingsLemma5
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  h5fin : ZInQ.DefFaltings.StableHeightFinite

/-- `ResearchLeaves4` gives `ResearchLeaves3` (the old R10 is a projection of the amended one). -/
theorem ResearchLeaves4.toR3 (r : ResearchLeaves4) : ResearchLeaves3 :=
  { r1r2 := r.r1r2, r1rec := r.r1rec, r3 := r.r3, r4 := r.r4, r5 := r.r5, r5count := r.r5count,
    r6 := r.r6, r7a := r.r7a, r7b := r.r7b, r8 := r.r8, r9a := r.r9a, r9b := r.r9b,
    r10 := ZInQ.Contrib.R10.deRhamComparison_of_HT r.r10, r11r12 := r.r11r12, r13 := r.r13,
    r14 := r.r14, r15 := r.r15, r16 := r.r16, r18 := r.r18, r19 := r.r19, r20 := r.r20,
    r21 := r.r21, r22 := r.r22, h5fin := r.h5fin }

/-- `ResearchLeaves3` together with g9-derham's `R10Weights` (the old field 28b of `GluePieces3`) gives
`ResearchLeaves4` (`deRhamComparisonHT_iff`). -/
theorem researchLeaves4_of (r : ResearchLeaves3) (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) :
    ResearchLeaves4 :=
  { r1r2 := r.r1r2, r1rec := r.r1rec, r3 := r.r3, r4 := r.r4, r5 := r.r5, r5count := r.r5count,
    r6 := r.r6, r7a := r.r7a, r7b := r.r7b, r8 := r.r8, r9a := r.r9a, r9b := r.r9b,
    r10 := ZInQ.Contrib.R10.deRhamComparisonHT_iff.mpr ⟨r.r10, hW⟩, r11r12 := r.r11r12,
    r13 := r.r13, r14 := r.r14, r15 := r.r15, r16 := r.r16, r18 := r.r18, r19 := r.r19,
    r20 := r.r20, r21 := r.r21, r22 := r.r22, h5fin := r.h5fin }

/-- **The named Props left after g0-assemble3.** -/
structure GluePieces4 : Prop where
  -- FibreSimple: FS5 (NoCM on the fibre)
  /-- fs5-nocm, LEAF (N1b′: CM points via optimal embeddings; Shimura 1967, Jordan, González–Rotger). -/
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  /-- fs5-nocm, GLUE (N2: the Kummer fibre of `X₆ → P¹` over `t(u)`). -/
  x6KummerFibre : FS5NoCM.X6KummerFibre
  -- ProductModelHeight (unif-dims, product-unif, infra-smooth-dim)
  /-- metrization (via unif-dims), LEAF (the uniformization theorem with its dimension: `𝒢(ℂ)_τ ≅ ℂ^g/Λ`,
  Mumford §1, §4; GAGA). -/
  analyticUniformizationOfDim : ZInQ.Metrization.AnalyticUniformizationOfDim
  -- StableHeightBaseChange (height-bc; infra-stalks proved the other two)
  /-- height-bc, GLUE (BC-alg: `ψ` is injective on the Hodge line). -/
  hodgeBCInjective : ZInQ.HeightBC.HodgeBCInjective
  /-- height-bc, GLUE (`ω` base-changes along `𝓞_L → 𝓞_{L'}`). -/
  omegaBaseChange : ZInQ.HeightBC.OmegaBaseChange
  -- ThetaPoint (g0-thetapoint, fibre-qm-period, period-map)
  /-- g0-thetapoint, LEAF? (theta-constant ratios at a period matrix are algebraic; Shimura 1976). -/
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- pkg-I1 (via fibre-qm-period), LEAF? (the theta-quotient Hauptmodul of `Γ*`). -/
  qmHauptmodul : PkgI1.QMHauptmodul
  /-- fibre-qm-period, LEAF (Eichler class number one for `𝒪`, lattice form). -/
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  /-- fibre-qm-period, LEAF (R1(b) in family form; Shimura 1967 Main Thm I). -/
  r1bFamily : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.R1bFamily (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- period-map, GLUE (base change of QM classes is unique). -/
  baseChangeClassUnique : G0Split.FibreQM.PeriodMapH.BaseChangeClassUnique
  /-- period-map, GLUE (`π` is invariant under the QM twist, complex form), for the leaf's own triple. -/
  piTwistC : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.PeriodMapH.PiTwistC (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- period-map, GLUE (the QM twist acts on the period lattice). -/
  qmTwistLattice : G0Split.FibreQM.PeriodMapH.QMTwistLattice
  /-- period-map, LEAF? (CM points descend; Shimura's theory of CM). -/
  cmDescends : G0Split.FibreQM.PeriodMapH.CMDescends
  /-- period-map, GLUE (numerical: `Σθ⁸(Ω(√2 + i)) ≠ 0`). -/
  s8Nonzero : G0Split.FibreQM.PeriodMap.S8Nonzero
  /-- period-map, GLUE (textbook complex analysis: a holomorphic map of the sphere factoring affinely). -/
  sphereFactorAffine : G0Split.FibreQM.PeriodMap.SphereFactorAffine
  /-- period-map, GLUE (`Σθ⁸∘Ω` has exact weight 8). -/
  s8WeightExact : G0Split.FibreQM.PeriodMap.S8WeightExact
  /-- period-map, LEAF (the valence formula for `Γ*`). -/
  valenceBoundGammaStar : G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar
  /-- fibre-qm-period, GLUE (transport of complex points along base change). -/
  cPtsTransport : G0Split.FibreQM.CPtsTransport
  -- ModularConstituent: G2 (fibre-cover; Prop. TS by prop-ts, prop-ts-glue)
  /-- prop-ts-glue, GLUE. -/ verticalResidueSeparable : PropTSGlue.VerticalResidueSeparable
  /-- prop-ts-glue, GLUE. -/ snSpecialize : PropTSGlue.SNSpecialize
  /-- prop-ts-glue, GLUE. -/ kummerCompositum : PropTSGlue.KummerCompositum
  /-- prop-ts-glue, GLUE (`AbhyankarDVR → …`). -/ kummerAbhyankarFinGlue : PropTSGlue.KummerAbhyankarFinGlue
  /-- prop-ts-glue, GLUE. -/ kummerOtherBranchFin : PropTSGlue.KummerOtherBranchFin
  /-- prop-ts-glue, GLUE. -/ kummerVerticalFin : PropTSGlue.KummerVerticalFin
  /-- prop-ts-glue, GLUE (`AbhyankarDVR → …`). -/ kummerAbhyankarInfGlue : PropTSGlue.KummerAbhyankarInfGlue
  /-- prop-ts-glue, GLUE. -/ kummerOtherBranchInf : PropTSGlue.KummerOtherBranchInf
  /-- prop-ts-glue, GLUE. -/ kummerVerticalInf : PropTSGlue.KummerVerticalInf
  /-- prop-ts-glue, GLUE (truth SPECULATIVE per its report). -/ heckeIrreducible : PropTSGlue.HeckeIrreducible
  /-- prop-ts-glue, GLUE. -/ heckeNormalizationIrr : PropTSGlue.HeckeNormalizationIrr
  /-- prop-ts-glue, GLUE. -/ heckeDegree : PropTSGlue.HeckeDegree
  /-- prop-ts-glue, GLUE. -/ heckeBranch : PropTSGlue.HeckeBranch
  /-- prop-ts-glue, GLUE (Lemma NV). -/ heckeNoVertRam : PropTSGlue.HeckeNoVertRam
  /-- fibre-cover, GLUE (a compositum of conjugates of a field unramified at `p` is unramified at `p`). -/
  unramifiedConjugates : G0ModField.UnramifiedConjugates
  -- ModularConstituent: G4 (kernel-field, kf-glue)
  /-- kf-glue, GLUE (Galois descent of the twisted isomorphisms). -/
  twistDescent : G0ModField.KernelField.TwistDescent
  -- ModularConstituent: G8-G12
  /-- g0-mod-galois, LEAF (R14 with its determinant clause; Shimura 1971 Thm 7.14; Deligne 1971). -/
  r14Det : G0Galois.R14Det
  /-- conj-twist, LEAF (N2: homomorphisms lift to `ℂ`-linear maps of uniformizations; Birkenhake–Lange 1.2.1). -/
  homLinearLift : G0Galois.HomLinearLift
  /-- g12-det, LEAF (HT weights of a twist shift by a constant; Sen 1980). -/
  senTwist : G0Galois.SenTwist
  /-- g12-det, LEAF (finite image ⇒ HT with weights 0; Tate 1967; Ax–Sen–Tate). -/
  finiteImageHT : G0Galois.FiniteImageHT
  /-- weil-pairing (used by g12-det), LEAF (T9 restated; Mumford §§6, 8, 20, 23). -/
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  /-- weil-pairing, LEAF (Mumford §7-8). -/
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  /-- weil-pairing, LEAF (Mumford §4 Appl. 2). -/
  divisiblePoints : WeilPairing.DivisiblePoints
  -- ModularConstituent: G13-G16
  /-- R17 concretely, LEAF (Carayol 1986, Thm (A)). -/
  carayolR17 : LadicCond.CarayolR17'
  -- ModularConstituent: joint glue on G7's data (linked-tate)
  /-- linked-tate, GLUE (G3 on the QM model: inertia above `p ∉ {3, ℓ}` fixes `ℓⁿ`-torsion, given NOS). -/
  goodRedTorsion : LinkedTate.GoodRedTorsion
  /-- linked-tate, GLUE (literature-backed: `rank End = 4` for a QM model with `EndDivision`). -/
  qmEndRank : LinkedTate.QMEndRank
  /-- linked-tate, GLUE (g14-trace's Frobenius link for the canonical operators). -/
  linkedFrob : UnramTate.LinkedFrob
  /-- linked-tate, GLUE (the upper breaks of the kernel field `L'`; usable since `G7Data` now carries
  `[L:ℚ] ≤ D`). -/
  kernelFieldBreaks : UnramTate.KernelFieldBreaks
  /-- linked-tate, GLUE (D1-D2 at `p = 3` for `ρ₅`). -/
  tateRamAtThree : UnramTate.TateRamAtThree

/-- `MobiusGlue` from T5 alone (image-plane). -/
theorem mobiusGlue_of_t5' (t : TextbookLeaves) : LeafQM.AV.Pin.MobiusGlue :=
  LeafQM.AV.CurveGlue.mobiusGlue_of_t5 t.t5

/-- FS5 (NoCM on the fibre) from `GluePieces4` (fs5-nocm). -/
theorem fibreComTrivial_of_gp4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    G0FibreSimple.FibreComTrivial :=
  fibreComTrivial_of_full (FS5NoCM.fibreComTrivialFull_of_leaves'' (r1r2fpFull_of r.toR3)
    (mobiusGlue_of_t5' t) t.t27 t.t6 gp.cmOptimalEmbedding gp.x6KummerFibre r.r5count)

/-- `FibreSimple` from `GluePieces4` (fs1-descend, mul-rigidity, infra-stalks' `MulIsogeny`, fs5-nocm). -/
theorem fibreSimple_of_gp4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    G0Split.FibreSimple :=
  G0FibreSimple.fibreSimple_of_leaves t MulRigidity.mulIsogeny G0FibreSimple.rigidityHom
    ⟨G0FibreSimple.finiteDescends_proof, fibreComTrivial_of_gp4 r t gp⟩

/-- G3 for `QML3` objects (linked-tate). -/
theorem qmModelG3_of_gp4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    LinkedTate.QMModelG3 :=
  LinkedTate.qmModelG3_of r.r7a r.r6 t.t5 (LinkedTate.goodRedG3Bridge_of_torsion gp.goodRedTorsion)

/-- Prop. TS for every admissible cover (prop-ts, prop-ts-glue). -/
theorem propTSAll_of_gp4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    G0ModField.PropTSAll :=
  PropTSGlue.propTSAll_of_pieces'' t.t2 (LeafAdopt.R1R2fp_of_rep r.r1r2) (mobiusGlue_of_t5' t)
    gp.verticalResidueSeparable gp.snSpecialize gp.kummerCompositum gp.kummerAbhyankarFinGlue
    gp.kummerOtherBranchFin gp.kummerVerticalFin gp.kummerAbhyankarInfGlue gp.kummerOtherBranchInf
    gp.kummerVerticalInf gp.heckeIrreducible gp.heckeNormalizationIrr gp.heckeDegree gp.heckeBranch
    gp.heckeNoVertRam

/-- The period map's glue for the leaf's own triple (period-map). -/
theorem periodMapGlue_of_gp4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep r.r1r2))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep r.r1r2))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep r.r1r2)) :=
  G0Split.FibreQM.PeriodMapH.periodMapGlue_own _ gp.baseChangeClassUnique (gp.piTwistC r.r1r2)
    gp.qmTwistLattice
    (G0Split.FibreQM.PeriodMapH.piCMC_of _ _ _ (G0Split.FibreQM.own_spec _).1
      (G0Split.FibreQM.own_spec _).2.2 gp.baseChangeClassUnique (gp.piTwistC r.r1r2) gp.cmDescends)
    (G0Split.FibreQM.PeriodMapH.cmFixedHasCM_of t.t11a)

/-- **`GluePieces` from `GluePieces4` and the leaf bundles** (g0-assemble3). -/
theorem gluePieces_of_gluePieces4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    GluePieces where
  dimFinite := G0Split.dimFinite
  dimBaseChange := G0Split.dimBaseChange
  fibreSimple := fibreSimple_of_gp4 r t gp
  productModelHeight := ZInQ.UnifDims.productModelHeight_of_unifOfDim gp.analyticUniformizationOfDim
  stableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine
    (ZInQ.HeightBC.g0_hodgeLine_iff.mpr (ZInQ.HeightBC.hodgeLineBaseChange_of_two
      gp.hodgeBCInjective gp.omegaBaseChange))
  productExists := G0Product.productExists
  reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3 r.toR3 G0Split.dimFinite
  thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios
    (G0Split.FibreQM.fibreQMPeriod_main_rep r.r1r2 (mobiusGlue_of_t5' t) gp.qmHauptmodul
      t.t35 t.t11a gp.qmClassNumberOne (gp.r1bFamily r.r1r2) (periodMapGlue_of_gp4 r t gp)
      (G0Split.FibreQM.PeriodMap.hauptmodulUnique_of' gp.s8Nonzero gp.sphereFactorAffine)
      (G0Split.FibreQM.PeriodMap.qmDenZeroCM3_of'' gp.s8Nonzero gp.s8WeightExact
        gp.valenceBoundGammaStar)
      gp.cPtsTransport)
    gp.thetaRatiosAlgebraic
  modularConstituent := modularConstituent_of_field t
    (G0ModField.fibreCoverExists_of_propTSAll' t.t5 (propTSAll_of_gp4 r t gp)
      gp.unramifiedConjugates)
    (G0ModField.KernelField.kernelFieldExists_of_descent t.t6 r.r7a r.r6 t.t5 t.t27
      (fibreComTrivial_of_gp4 r t gp) MulRigidity.mulIsogeny gp.twistDescent)
    UnramTate.unramifiedSup_mf
    (G0AssembleMod.afterG7_of3 r.toR3 t
      ⟨RvGP2.burnsideAbsIrred, gp.r14Det,
        ZInQ.Contrib.R10.g9Glue_of_deRhamComparisonHT r.r10,
        G0Galois.g10Glue_of_conjTwist
          (G0Galois.conjTwistNontrivial_of_leaves t.t5 t.t26 t.t35 gp.homLinearLift),
        G0Galois.g12Weight_of_senTwist gp.senTwist gp.finiteImageHT,
        G0Galois.detTate_of_leaves gp.t09SymmIsogenyExists gp.isogenyQuasiInverse
          gp.divisiblePoints t.t26,
        G0AssembleMod.resQFiniteIndex⟩
      (G0ModNewform.dirichletOfFinite_of_t17 t.t17) gp.carayolR17
      Swan.swanIndependent_proved Swan.swanIntegral_proved
      Swan.adaptedExists_proved
      (LinkedTate.modelG3G6_of (fibreSimple_of_gp4 r t gp) (qmModelG3_of_gp4 r t gp))
      (LinkedTate.linkedTateData_of_frobRam t.t7 t.t26 (fibreSimple_of_gp4 r t gp) gp.qmEndRank
        (UnramTate.linkedFrobRam_of gp.linkedFrob
          (UnramTate.linkedRam_of (qmModelG3_of_gp4 r t gp) gp.kernelFieldBreaks
            UnramTate.localInertiaGlobal UnramTate.upperAbsInertia gp.tateRamAtThree))))
  heightCopies := G0HeightCopies.heightCopiesAgree

/-- **G0 after g0-assemble3**: the leaf bundles (`ResearchLeaves4`, `TextbookLeaves`) and `GluePieces4` imply
`ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leavesR3 r.toR3 t (gluePieces_of_gluePieces4 r t gp)

/-- The same with g0-assemble2's `ResearchLeaves3` and the weight clause `R10Weights`. -/
theorem sixContactMin_of_leaves4' (r : ResearchLeaves3) (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights)
    (t : TextbookLeaves) (gp : GluePieces4) : ZInQ.SixContactMin :=
  sixContactMin_of_leaves4 (researchLeaves4_of r hW) t gp

end HSyn

end

#print axioms HSyn.gluePieces_of_gluePieces4
#print axioms HSyn.sixContactMin_of_leaves4
#print axioms HSyn.sixContactMin_of_leaves4'
#print axioms HSyn.ResearchLeaves4.toR3
#print axioms ZInQ.UnifDims.productModelHeight_of_unifOfDim
#print axioms MulRigidity.mulIsogeny
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_t5
#print axioms RvGP2.burnsideAbsIrred
#print axioms G0ModField.KernelField.endTransport
#print axioms G0ModField.KernelField.oMaximal
#print axioms ZInQ.Contrib.R10.g9Glue_of_deRhamComparisonHT
#print axioms G0Galois.conjTwistNontrivial_of_leaves
#print axioms ZInQ.HeightBC.cotangentSpanBC
#print axioms ZInQ.HeightBC.uniformizationLiftAnalytic
#print axioms ZInQ.ProductUnif.productUnifSplits
#print axioms ZInQ.DefFaltings.HodgeLattice.tangentDimAtOrigin
#print axioms PropTSGlue.propTSAll_of_pieces''
#print axioms HSyn.LinkedTate.linkedTateData_of_frobRam
