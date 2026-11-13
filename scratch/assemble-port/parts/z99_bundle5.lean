/-! ## assemble-port: `GluePieces5`, `gluePieces_of_gluePieces5`, `sixContactMin_of_leaves5`

Task assemble-port, 2026-11-13. g0-assemble3's `sixContactMin_of_leaves4` (part z95), ported onto leaf-fold2's base
(`scratch/h-decomposition/Leaves.lean` with the ten unused `TextbookLeaves` fields deleted, every part inside `namespace
HDec`; leaf-fold2's bundles `OpenResearchLeaves2`, `OpenTextbookLeaves2`, part z98), with the results proved since
g0-assemble3 folded in: prop-ts-glue's `SpecNonMeeting` (part e10), ts-kummer (e12), hodge-bc2 (b15), leaf-fold2's T35
transport (e40), cpts-transport (e45), lt-goodred (z96), linked-ram (z97). -/

noncomputable section

namespace HSyn

open G0Split

/-- leaf-fold2's research bundle gives g0-assemble3's `ResearchLeaves4`: R14 without its determinant clause
(`eigenformRepExists_of_r14Det`); leaf-fold's `PkgI4.DeRhamComparisonHT` is accepted as r10-amend's
`ZInQ.Contrib.R10.DeRhamComparisonHT` (the same statement, two copies; definitional unfolding). -/
theorem researchLeaves4_of_open2 (r : OpenResearchLeaves2) : ResearchLeaves4 :=
  { r1r2 := r.r1r2, r1rec := r.r1rec, r3 := r.r3, r4 := r.r4, r5 := r.r5, r5count := r.r5count, r6 := r.r6,
    r7a := r.r7a, r7b := r.r7b, r8 := r.r8, r9a := r.r9a, r9b := r.r9b, r10 := r.r10, r11r12 := r.r11r12,
    r13 := r.r13, r14 := eigenformRepExists_of_r14Det r.r14, r15 := r.r15, r16 := r.r16, r18 := r.r18,
    r19 := r.r19, r20 := r.r20, r21 := r.r21, r22 := r.r22, h5fin := r.h5fin }

/-- **The named Props left after assemble-port** (27 fields). g0-assemble3's `GluePieces4` (46 fields) without the 24
fields proved or moved since (table: docs/research/assemble-port.md §2), plus linked-ram's `upperBreakBound` (LEAF?) and
`betaTrivialAtTwo` (GLUE), which replace `kernelFieldBreaks`, and linked-ram's corrected `tateRamAtThreeD` (GLUE), which
replaces `tateRamAtThree` (not quantified over `G7Data`, so without `[L:ℚ] ≤ D`; likely false as stated, linked-ram F1),
and period-glue's leaves `gammaStarGen` (LEAF?) and `t11aRiemannHom` (LEAF), which replace `s8WeightExact` and
`qmTwistLattice`. -/
structure GluePieces5 : Prop where
  -- FibreSimple: FS5 (NoCM on the fibre)
  /-- fs5-nocm, LEAF (N1b′: CM points via optimal embeddings; Shimura 1967, Jordan, González–Rotger). -/
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  /-- x6-kummer, LEAF (N2-L′: `X₆` is the conic `Y² + 3X² + 3Z² = 0` with `π₆ = −16(X² + Z²)/(27Z²)` on
  `ℚ̄`-points of one witness of the leaf bundle; Elkies 1998 §3, Kurihara 1979; a consequence of the published model,
  x6-kummer §3.6). fs5-nocm's glue N2 `X6KummerFibre` is proved from it and `MobiusGlue`. -/
  x6ConicModel : X6Kummer.X6ConicModel
  -- ProductModelHeight (unif-dims, product-unif, infra-smooth-dim)
  -- StableHeightBaseChange (height-bc; infra-stalks proved the other two)
  -- ThetaPoint (g0-thetapoint, fibre-qm-period, period-map)
  /-- g0-thetapoint, LEAF? (theta-constant ratios at a period matrix are algebraic; Shimura 1976). -/
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- pkg-I1 (via fibre-qm-period), LEAF? (the theta-quotient Hauptmodul of `Γ*`). -/
  qmHauptmodul : PkgI1.QMHauptmodul
  /-- fibre-qm-period, LEAF (Eichler class number one for `𝒪`, lattice form). -/
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  /-- period-map, GLUE (`π` is invariant under the QM twist, complex form), for the leaf's own triple. -/
  piTwistC : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.PeriodMapH.PiTwistC (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- period-map, LEAF? (CM points descend; Shimura's theory of CM). -/
  cmDescends : G0Split.FibreQM.PeriodMapH.CMDescends
  /-- period-map, GLUE (textbook complex analysis: a holomorphic map of the sphere factoring affinely). -/
  sphereFactorAffine : G0Split.FibreQM.PeriodMap.SphereFactorAffine
  /-- period-map, LEAF (the valence formula for `Γ*`). -/
  valenceBoundGammaStar : G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar
  -- ModularConstituent: G2 (fibre-cover; Prop. TS by prop-ts, prop-ts-glue)
  /-- prop-ts-glue, GLUE. -/ kummerCompositum : PropTSGlue.KummerCompositum
  /-- prop-ts-glue, GLUE (truth SPECULATIVE per its report). -/ heckeIrreducible : PropTSGlue.HeckeIrreducible
  /-- prop-ts-glue, GLUE. -/ heckeNormalizationIrr : PropTSGlue.HeckeNormalizationIrr
  /-- prop-ts-glue, GLUE. -/ heckeDegree : PropTSGlue.HeckeDegree
  /-- prop-ts-glue, GLUE. -/ heckeBranch : PropTSGlue.HeckeBranch
  /-- prop-ts-glue, GLUE (Lemma NV). -/ heckeNoVertRam : PropTSGlue.HeckeNoVertRam
  -- ModularConstituent: G4 (kernel-field, kf-glue)
  -- ModularConstituent: G8-G12
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
  -- ModularConstituent: joint glue on G7's data (linked-tate)
  /-- linked-tate, GLUE (g14-trace's Frobenius link for the canonical operators). -/
  linkedFrob : UnramTate.LinkedFrob
  /-- linked-ram, LEAF? (textbook composite: the absolute upper-break bound `4a²` for a degree-`a` extension of `ℚ_p`;
  Glazer L796-811 from Serre, *Local Fields*, III §6 and IV §1-§3). With `BetaTrivialAtTwo` it gives linked-tate's
  `KernelFieldBreaks` (`UnramTate.kernelFieldBreaks_of'`). -/
  upperBreakBound : UnramTate.UpperBreakBound
  /-- linked-ram, GLUE (`β` trivial on `G_{ℚ_2}^u ∩ G_L`, `u > U₀`; Glazer L826-843, local reciprocity). -/
  betaTrivialAtTwo : UnramTate.BetaTrivialAtTwo
  /-- linked-ram, GLUE (corrected field 46: `TateRamAtThree` with the hypothesis `[L:ℚ] ≤ D`, D1-D2 at `p = 3` for
  `ρ₅`; implied by the old field, `tateRamAtThreeD_of`). -/
  tateRamAtThreeD : UnramTate.TateRamAtThreeD
  /-- period-glue, LEAF? (`Γ*/ℚ^×` is the `(2,4,6)` triangle group generated by `ι(1+i+j)`, `ι((j−3)/2)`: Takeuchi 1977,
  Elkies 1998 §3, Poincaré's polygon theorem; with R4 it gives period-map's `S8WeightExact`, `s8WeightExact_of`). -/
  gammaStarGen : G0Split.FibreQM.PeriodGlue.GammaStarGen
  /-- period-glue, LEAF (T11(a) in `Hom` form: homomorphisms of complex abelian varieties are the lattice-preserving
  `ℂ`-linear maps; Mumford §1, Birkenhake–Lange 1.2.1, GAGA; with Skolem–Noether, proved, it gives period-map's
  `QMTwistLattice`, `qmTwistLattice_of'`). -/
  t11aRiemannHom : G0Split.FibreQM.PeriodGlue.T11aRiemannHom

/-- **`GluePieces` from `GluePieces5` and leaf-fold2's open leaf bundles.** g0-assemble3's `gluePieces_of_gluePieces4`
(part z95), with every field proved since replaced by its proof: `analyticUniformizationOfDim` by T35's transport,
`hodgeBCInjective`, `omegaBaseChange` (hodge-bc2), `baseChangeClassUnique`, `cPtsTransport` (cpts-transport),
`SpecNonMeeting` and six Kummer pieces inside `propTSAll_final''` (prop-ts-glue, ts-kummer), `goodRedTorsion`,
`qmEndRank` (lt-goodred), `KernelFieldBreaks` (linked-ram, from `upperBreakBound`, `betaTrivialAtTwo`), `twistDescent` (twist-descent), `s8Nonzero`
(period-glue), `s8WeightExact`, `qmTwistLattice` (period-glue, from `gammaStarGen`, `t11aRiemannHom` and the proved
Skolem–Noether), linked-tate's
`LinkedRam` through linked-ram's `linkedRam_of'` with the corrected `tateRamAtThreeD`; `r1bFamily`, `r14Det`, `carayolR17` are the fields `r1b`, `r14`, `r17` of
`OpenResearchLeaves2`. -/
theorem gluePieces_of_gluePieces5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5) :
    GluePieces :=
  let r4 := researchLeaves4_of_open2 r
  let t3 := textbookLeaves_of_open2 t
  have hMob : LeafQM.AV.Pin.MobiusGlue := mobiusGlue_of_t5' t3
  have hFS5 : G0FibreSimple.FibreComTrivial :=
    fibreComTrivial_of_full (FS5NoCM.fibreComTrivialFull_of_leaves'' (r1r2fpFull_of r4.toR3)
      hMob t.t27 t.t6 gp.cmOptimalEmbedding
      (X6Kummer.x6KummerFibre_of_conic hMob gp.x6ConicModel) r.r5count)
  have hFS : G0Split.FibreSimple :=
    G0FibreSimple.fibreSimple_of_leaves t3 MulRigidity.mulIsogeny G0FibreSimple.rigidityHom
      ⟨G0FibreSimple.finiteDescends_proof, hFS5⟩
  have hG3 : LinkedTate.QMModelG3 :=
    LinkedTate.qmModelG3_of r.r7a r.r6 t.t5 (LinkedTate.goodRedG3Bridge_of_torsion LTGoodRed.goodRedTorsion)
  have hTS : G0ModField.PropTSAll :=
    PropTSGlue.propTSAll_final'' t2_proved (LeafAdopt.R1R2fp_of_rep r.r1r2) hMob gp.kummerCompositum
      TsKummer.kummerAbhyankarFinGlue TsKummer.kummerOtherBranchFin TsKummer.kummerVerticalFin
      TsKummer.kummerAbhyankarInfGlue TsKummer.kummerOtherBranchInf TsKummer.kummerVerticalInf
      gp.heckeIrreducible gp.heckeNormalizationIrr gp.heckeDegree gp.heckeBranch gp.heckeNoVertRam
  have hPM : G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep r.r1r2))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep r.r1r2))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep r.r1r2)) :=
    G0Split.FibreQM.PeriodMapH.periodMapGlue_own _ G0Split.FibreQM.PeriodMapH.baseChangeClassUnique_proof
      (gp.piTwistC r.r1r2) (G0Split.FibreQM.PeriodGlue.qmTwistLattice_of' gp.t11aRiemannHom TSkolemKW.glueDescent_leafSkolemNoether)
      (G0Split.FibreQM.PeriodMapH.piCMC_of _ _ _ (G0Split.FibreQM.own_spec _).1
        (G0Split.FibreQM.own_spec _).2.2 G0Split.FibreQM.PeriodMapH.baseChangeClassUnique_proof
        (gp.piTwistC r.r1r2) gp.cmDescends)
      (G0Split.FibreQM.PeriodMapH.cmFixedHasCM_of t.t11a)
  { dimFinite := G0Split.dimFinite
    dimBaseChange := G0Split.dimBaseChange
    fibreSimple := hFS
    productModelHeight := ZInQ.UnifDims.productModelHeight_of_unifOfDim
      (ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists t.t35)
    stableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine
      (ZInQ.HeightBC.g0_hodgeLine_iff.mpr (ZInQ.HeightBC.hodgeLineBaseChange_of_two
        ZInQ.HeightBC.hodgeBCInjective ZInQ.HeightBC.omegaBaseChange))
    productExists := G0Product.productExists
    reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3 r4.toR3 G0Split.dimFinite
    thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios
      (G0Split.FibreQM.fibreQMPeriod_main_rep r.r1r2 hMob gp.qmHauptmodul
        t.t35 t.t11a gp.qmClassNumberOne (r.r1b r.r1r2) hPM
        (G0Split.FibreQM.PeriodMap.hauptmodulUnique_of' G0Split.FibreQM.PeriodGlue.s8Nonzero_proof gp.sphereFactorAffine)
        (G0Split.FibreQM.PeriodMap.qmDenZeroCM3_of'' G0Split.FibreQM.PeriodGlue.s8Nonzero_proof (G0Split.FibreQM.PeriodGlue.s8WeightExact_of r.r4 gp.gammaStarGen)
          gp.valenceBoundGammaStar)
        G0Split.FibreQM.cPtsTransport_proof)
      gp.thetaRatiosAlgebraic
    modularConstituent := modularConstituent_of_field t3
      (G0ModField.fibreCoverExists_of_propTSAll' t.t5 hTS G0ModField.unramifiedConjugates)
      (G0ModField.KernelField.kernelFieldExists_of_descent t.t6 r.r7a r.r6 t.t5 t.t27
        hFS5 MulRigidity.mulIsogeny G0ModField.KernelField.twistDescent)
      UnramTate.unramifiedSup_mf
      (G0AssembleMod.afterG7_of3 r4.toR3 t3
        ⟨RvGP2.burnsideAbsIrred, r.r14,
          ZInQ.Contrib.R10.g9Glue_of_deRhamComparisonHT r4.r10,
          G0Galois.g10Glue_of_conjTwist
            (G0Galois.conjTwistNontrivial_of_leaves t.t5 t.t26 t.t35 gp.homLinearLift),
          G0Galois.g12Weight_of_senTwist gp.senTwist gp.finiteImageHT,
          G0Galois.detTate_of_leaves gp.t09SymmIsogenyExists gp.isogenyQuasiInverse
            gp.divisiblePoints t.t26,
          G0AssembleMod.resQFiniteIndex⟩
        (G0ModNewform.dirichletOfFinite_of_t17 t17_proved) r.r17
        Swan.swanIndependent_proved Swan.swanIntegral_proved
        Swan.adaptedExists_proved
        (LinkedTate.modelG3G6_of hFS hG3)
        (LinkedTate.linkedTateData_of_frobRam t.t7 t.t26 hFS
          (LTGoodRed.QM.qmEndRank_of_leaves t.t6 t.t27)
          (UnramTate.linkedFrobRam_of gp.linkedFrob
            (UnramTate.linkedRam_of' hG3
              (UnramTate.kernelFieldBreaks_of' gp.upperBreakBound gp.betaTrivialAtTwo)
              UnramTate.localInertiaGlobal UnramTate.upperAbsInertia
              gp.tateRamAtThreeD))))
    heightCopies := G0HeightCopies.heightCopiesAgree }

/-- **G0 after assemble-port** (no `sorry`, standard axioms): leaf-fold2's open research leaves (`OpenResearchLeaves2`,
26 fields), its open textbook leaves (`OpenTextbookLeaves2`, 18 fields) and `GluePieces5` (27 fields: 11 LEAF, 5 LEAF?,
11 GLUE; table in docs/research/assemble-port.md §2) imply `ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leavesR3 (researchLeaves4_of_open2 r).toR3 (textbookLeaves_of_open2 t)
    (gluePieces_of_gluePieces5 r t gp)

end HSyn

end

#print axioms HSyn.researchLeaves4_of_open2
#print axioms HSyn.gluePieces_of_gluePieces5
#print axioms HSyn.sixContactMin_of_leaves5
#print axioms HSyn.textbookLeaves_of_open2
#print axioms HSyn.t14a_proved
#print axioms HSyn.t14b_proved
#print axioms HSyn.t36_proved
#print axioms HSyn.t37_proved
#print axioms HSyn.t39_of_t40
#print axioms PropTSGlue.specNonMeeting
#print axioms PropTSGlue.propTSAll_final''
#print axioms ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists
#print axioms ZInQ.HeightBC.hodgeBCInjective
#print axioms ZInQ.HeightBC.omegaBaseChange
#print axioms HSyn.G0Split.FibreQM.cPtsTransport_proof
#print axioms HSyn.G0Split.FibreQM.PeriodMapH.baseChangeClassUnique_proof
#print axioms TsKummer.kummerAbhyankarFinGlue
#print axioms TsKummer.kummerOtherBranchFin
#print axioms TsKummer.kummerVerticalFin
#print axioms TsKummer.kummerAbhyankarInfGlue
#print axioms TsKummer.kummerOtherBranchInf
#print axioms TsKummer.kummerVerticalInf
#print axioms LTGoodRed.goodRedTorsion
#print axioms LTGoodRed.QM.qmEndRank_of_leaves
#print axioms UnramTate.kernelFieldBreaks_of'
#print axioms UnramTate.linkedRam_of'
#print axioms UnramTate.kernelFieldBreaksHigh
#print axioms G0ModField.KernelField.twistDescent
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.s8Nonzero_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.s8WeightExact_of
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.qmTwistLattice_of'
#print axioms UnramTate.upperAbsWild
