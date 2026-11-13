/-! ## assemble-port: `GluePieces5`, `sixContactMin_of_leaves5`

Task assemble-port, 2026-11-13. g0-assemble3's `sixContactMin_of_leaves4` (part z95), ported onto leaf-fold2's base
(`scratch/h-decomposition/Leaves.lean` with the ten unused `TextbookLeaves` fields deleted, every part in `namespace
HDec`; leaf-fold2's bundles `OpenResearchLeaves2`, `OpenTextbookLeaves2`, part z98), with prop-ts-glue's final results
(part e10 regenerated from `scratch/prop-ts-glue/PropTSGlue.lean` at 3d41b3d5): `VerticalResidueSeparable` and
`SNSpecialize` are theorems (so is `SpecNonMeeting`). -/

noncomputable section

namespace HSyn

/-- leaf-fold2's research bundle gives g0-assemble3's `ResearchLeaves4`: R14 without its determinant clause
(`eigenformRepExists_of_r14Det`); R10 amended in leaf-fold's form `PkgI4.DeRhamComparisonHT` is r10-amend's
`ZInQ.Contrib.R10.DeRhamComparisonHT` (the same statement, two copies; accepted by unfolding). -/
theorem researchLeaves4_of_open2 (r : OpenResearchLeaves2) : ResearchLeaves4 :=
  { r1r2 := r.r1r2,
    r1rec := r.r1rec,
    r3 := r.r3,
    r4 := r.r4,
    r5 := r.r5,
    r5count := r.r5count,
    r6 := r.r6,
    r7a := r.r7a,
    r7b := r.r7b,
    r8 := r.r8,
    r9a := r.r9a,
    r9b := r.r9b,
    r10 := r.r10,
    r11r12 := r.r11r12,
    r13 := r.r13,
    r14 := eigenformRepExists_of_r14Det r.r14,
    r15 := r.r15,
    r16 := r.r16,
    r18 := r.r18,
    r19 := r.r19,
    r20 := r.r20,
    r21 := r.r21,
    r22 := r.r22,
    h5fin := r.h5fin }

/-- **The named Props left after assemble-port** (41 fields): g0-assemble3's `GluePieces4` without
* `verticalResidueSeparable`, `snSpecialize`: proved by prop-ts-glue (`verticalResidueDegree`, `snSpecializeUnram`;
  together `PropTSGlue.specNonMeeting`);
* `r14Det`, `r1bFamily`, `carayolR17`: these leaves are fields of leaf-fold2's research bundle `OpenResearchLeaves2`
  (`r14`, `r1b`, `r17`), the same Props. -/
structure GluePieces5 : Prop where
  -- FibreSimple: FS5 (NoCM on the fibre)
  /-- fs5-nocm, LEAF (N1b′: CM points via optimal embeddings; Shimura 1967, Jordan, González–Rotger). -/
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  /-- x6-kummer, LEAF (N2-L′: `X₆` is the conic `Y² + 3X² + 3Z² = 0` with `π₆ = −16(X² + Z²)/(27Z²)` on
  `ℚ̄`-points of one witness of the leaf bundle; Elkies 1998 §3, Kurihara 1979; a consequence of the published model,
  x6-kummer §3.6). fs5-nocm's glue N2 `X6KummerFibre` is proved from it and `MobiusGlue`. -/
  x6ConicModel : X6Kummer.X6ConicModel
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
  -- ModularConstituent: G4 (kernel-field, kf-glue)
  /-- kf-glue, GLUE (Galois descent of the twisted isomorphisms). -/
  twistDescent : G0ModField.KernelField.TwistDescent
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


/-- **`GluePieces4` from `GluePieces5`** and leaf-fold2's research bundle. -/
theorem gluePieces4_of_gluePieces5 (r : OpenResearchLeaves2) (gp : GluePieces5) : GluePieces4 :=
  { verticalResidueSeparable := PropTSGlue.verticalResidueSeparable_of_degree PropTSGlue.verticalResidueDegree,
    snSpecialize := PropTSGlue.snSpecialize_of_unram PropTSGlue.snSpecializeUnram,
    r14Det := r.r14,
    r1bFamily := r.r1b,
    carayolR17 := r.r17,
    cmOptimalEmbedding := gp.cmOptimalEmbedding,
    x6ConicModel := gp.x6ConicModel,
    analyticUniformizationOfDim := gp.analyticUniformizationOfDim,
    hodgeBCInjective := gp.hodgeBCInjective,
    omegaBaseChange := gp.omegaBaseChange,
    thetaRatiosAlgebraic := gp.thetaRatiosAlgebraic,
    qmHauptmodul := gp.qmHauptmodul,
    qmClassNumberOne := gp.qmClassNumberOne,
    baseChangeClassUnique := gp.baseChangeClassUnique,
    piTwistC := gp.piTwistC,
    qmTwistLattice := gp.qmTwistLattice,
    cmDescends := gp.cmDescends,
    s8Nonzero := gp.s8Nonzero,
    sphereFactorAffine := gp.sphereFactorAffine,
    s8WeightExact := gp.s8WeightExact,
    valenceBoundGammaStar := gp.valenceBoundGammaStar,
    cPtsTransport := gp.cPtsTransport,
    kummerCompositum := gp.kummerCompositum,
    kummerAbhyankarFinGlue := gp.kummerAbhyankarFinGlue,
    kummerOtherBranchFin := gp.kummerOtherBranchFin,
    kummerVerticalFin := gp.kummerVerticalFin,
    kummerAbhyankarInfGlue := gp.kummerAbhyankarInfGlue,
    kummerOtherBranchInf := gp.kummerOtherBranchInf,
    kummerVerticalInf := gp.kummerVerticalInf,
    heckeIrreducible := gp.heckeIrreducible,
    heckeNormalizationIrr := gp.heckeNormalizationIrr,
    heckeDegree := gp.heckeDegree,
    heckeBranch := gp.heckeBranch,
    heckeNoVertRam := gp.heckeNoVertRam,
    twistDescent := gp.twistDescent,
    homLinearLift := gp.homLinearLift,
    senTwist := gp.senTwist,
    finiteImageHT := gp.finiteImageHT,
    t09SymmIsogenyExists := gp.t09SymmIsogenyExists,
    isogenyQuasiInverse := gp.isogenyQuasiInverse,
    divisiblePoints := gp.divisiblePoints,
    goodRedTorsion := gp.goodRedTorsion,
    qmEndRank := gp.qmEndRank,
    linkedFrob := gp.linkedFrob,
    kernelFieldBreaks := gp.kernelFieldBreaks,
    tateRamAtThree := gp.tateRamAtThree }

/-- **G0 after assemble-port** (no `sorry`, standard axioms): leaf-fold2's open research leaves (`OpenResearchLeaves2`,
26 fields) and open textbook leaves (`OpenTextbookLeaves2`, 18 fields) and `GluePieces5` (41 fields: 14 LEAF, 3 LEAF?,
24 GLUE; table in docs/research/assemble-port.md) imply `ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leaves4 (researchLeaves4_of_open2 r) (textbookLeaves_of_open2 t) (gluePieces4_of_gluePieces5 r gp)

end HSyn

end

#print axioms HSyn.researchLeaves4_of_open2
#print axioms HSyn.gluePieces4_of_gluePieces5
#print axioms HSyn.sixContactMin_of_leaves5
#print axioms HSyn.textbookLeaves_of_open2
#print axioms HSyn.t14a_proved
#print axioms HSyn.t14b_proved
#print axioms HSyn.t36_proved
#print axioms HSyn.t37_proved
#print axioms HSyn.t39_of_t40
#print axioms PropTSGlue.specNonMeeting
#print axioms PropTSGlue.verticalResidueDegree
#print axioms PropTSGlue.snSpecializeUnram
#print axioms PropTSGlue.propTSAll_final''
