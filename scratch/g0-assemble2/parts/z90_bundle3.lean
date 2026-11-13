/-! ## g0-assemble2: `GluePieces` from `GluePieces3`

Task g0-assemble2, 2026-11-13. g0-assemble's `GluePieces2` (27 fields) with every wave-27 result
applied (parts a10-a80 above). Each field of `GluePieces3` is a named `def … : Prop` of a wave-26
or wave-27 task, copied verbatim in that task's part; kinds and sources are in
`docs/research/g0-assemble2.md` §2 (LEAF = published theorem, LEAF? = leaf candidate, GLUE = to be
proved by the project). -/

noncomputable section

namespace HSyn

open G0Split

/-- **The named Props left after waves 26-27** (g0-assemble2). -/
structure GluePieces3 : Prop where
  -- FibreSimple (FS1-FS5)
  /-- mul-rigidity, LEAF (Mumford §4 Appl. 2, §6; Milne Thm 8.2, char 0; UNVERIFIED locators):
  `[n]` is étale for `n ≠ 0`. -/
  mulEtale : MulRigidity.MulEtale
  /-- fs5-nocm N1b′, LEAF (Shimura's description of CM points; UNVERIFIED locator). -/
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  /-- fs5-nocm N2, GLUE (Kummer fibre of `X₆`). -/
  x6KummerFibre : FS5NoCM.X6KummerFibre
  /-- curve-facts C1b, GLUE (dimension theory of smooth curves). -/
  smoothStalkDimOne : LeafQM.AV.Pin.SmoothStalkDimOne
  /-- curve-facts C2K, LEAF (Hartshorne II.6.8, UNVERIFIED numbering). -/
  constOrOntoAlgClosed : LeafQM.AV.Pin.ConstOrOntoAlgClosed
  /-- curve-facts C3K, GLUE (textbook consequence). -/
  ratFactorAlgClosed : LeafQM.AV.Pin.RatFactorAlgClosed
  -- ProductModelHeight (P2)
  /-- product-height S-an, GLUE (elementary analysis). -/
  productUnifSplits : ZInQ.ProductHeight.ProductUnifSplits
  /-- product-height S-alg, GLUE (Hodge theory of a product). -/
  productMetrizationOfProductUnif : ZInQ.ProductHeight.ProductMetrizationOfProductUnif
  -- StableHeightBaseChange (H4a)
  /-- height-bc, GLUE. -/
  hodgeBCInjective : ZInQ.HeightBC.HodgeBCInjective
  /-- height-bc, GLUE. -/
  cotangentSpanBC : ZInQ.HeightBC.CotangentSpanBC
  /-- height-bc, GLUE. -/
  omegaBaseChange : ZInQ.HeightBC.OmegaBaseChange
  /-- height-bc, GLUE. -/
  uniformizationLiftAnalytic : ZInQ.HeightBC.UniformizationLiftAnalytic
  -- ThetaPointOfFibre
  /-- g0-thetapoint, LEAF? (Shimura 1976 / Mumford Tata II; UNVERIFIED). -/
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- fibre-qm-period, LEAF? (pkg-I1's composite leaf). -/
  qmHauptmodul : PkgI1.QMHauptmodul
  /-- fibre-qm-period, LEAF (Eichler class number one, lattice form). -/
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  /-- fibre-qm-period, LEAF (R1(b) in family form), for the triple of the leaf bundle. -/
  r1bFamily : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.R1bFamily (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- fibre-qm-period, GLUE, for the triple of the leaf bundle. -/
  periodMapGlue : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- fibre-qm-period, GLUE. -/
  hauptmodulUnique : G0Split.FibreQM.HauptmodulUnique
  /-- fibre-qm-period, LEAF? (Lin–Yang's divisor of `ψ₄`). -/
  qmDenZeroCM3 : G0Split.FibreQM.QMDenZeroCM3
  /-- fibre-qm-period, GLUE. -/
  cPtsTransport : G0Split.FibreQM.CPtsTransport
  -- ModularConstituent: G2 (fibre-cover), G4 (kernel-field)
  /-- fibre-cover, GLUE (Prop. TS for every admissible cover). -/
  propTSAll : G0ModField.PropTSAll
  /-- fibre-cover, GLUE (Neukirch; compositum of conjugates). -/
  unramifiedConjugates : G0ModField.UnramifiedConjugates
  /-- kernel-field 4a′, GLUE (pure algebra: `𝒪` is maximal). -/
  oMaximal : G0ModField.KernelField.OMaximal
  /-- kernel-field 4b, GLUE. -/
  endTransport : G0ModField.KernelField.EndTransport
  /-- kernel-field, GLUE (the conjugacy maps, geometric part). -/
  conjIsogMaps : G0ModField.KernelField.ConjIsogMaps
  -- ModularConstituent: G8-G12 (g0-mod-galois, g10-odd, conj-twist, g12-det)
  /-- g0-mod-galois, LEAF (Burnside). -/
  burnsideAbsIrred : G0Galois.BurnsideAbsIrred
  /-- g0-mod-galois, LEAF (R14 with its determinant clause). -/
  r14Det : G0Galois.R14Det
  /-- g0-mod-galois G9, GLUE (de Rham descent lemma). -/
  g9Glue : G0Galois.G9Glue
  /-- conj-twist N1-surj, GLUE. -/
  artinTorsionSurj : G0Galois.ArtinTorsionSurj
  /-- conj-twist N2, LEAF (Birkenhake–Lange Prop. 1.2.1, UNVERIFIED). -/
  homLinearLift : G0Galois.HomLinearLift
  /-- conj-twist N3a, GLUE. -/
  conjUniformization : G0Galois.ConjUniformization
  /-- g12-det, LEAF (Sen 1980). -/
  senTwist : G0Galois.SenTwist
  /-- g12-det, LEAF (Tate 1967, Ax–Sen–Tate). -/
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
  -- ModularConstituent: joint glue on G7's data (g0-assemble)
  /-- g0-assemble, GLUE (G3 and G6 on G7's model). -/
  modelG3G6 : G0AssembleMod.ModelG3G6
  /-- g0-assemble2 (from g14-trace, g15-ram), GLUE: linked Tate data with the Frobenius link and
  the local data (replaces g0-assemble's `LinkedTateData`). -/
  linkedTateLocal : G0AssembleMod.LinkedTateLocal

/-- fs5-nocm's `R1R2fpFull` is the leaf bundle's `R1R2fp` after pin-apply (same clauses). -/
theorem r1r2fpFull_of (r : ResearchLeaves3) : FS5NoCM.R1R2fpFull := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h⟩ := LeafAdopt.R1R2fp_of_rep r.r1r2
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h⟩

/-- fs5-nocm's `FibreComTrivialFull` is g0-fibresimple's `FibreComTrivial` over Leaves.lean after
pin-apply (`R1fpPropsFull` and `R1fpProps` have the same text). -/
theorem fibreComTrivial_of_full (h : FS5NoCM.FibreComTrivialFull) :
    G0FibreSimple.FibreComTrivial :=
  fun Y Φ π h1 => h Y Φ π h1

/-- `MobiusGlue` from the curve facts (curve-facts, mobius-glue) and T5. -/
theorem mobiusGlue_of_gp3 (t : TextbookLeaves) (gp : GluePieces3) : LeafQM.AV.Pin.MobiusGlue :=
  LeafQM.AV.Pin.mobiusGlue_of_curves'
    (LeafQM.AV.Pin.curveFacts_of_leaves gp.smoothStalkDimOne gp.constOrOntoAlgClosed
      gp.ratFactorAlgClosed).1
    (LeafQM.AV.Pin.curveFacts_of_leaves gp.smoothStalkDimOne gp.constOrOntoAlgClosed
      gp.ratFactorAlgClosed).2
    t.t5

/-- FS5 (NoCM on the fibre) from `GluePieces3` (fs5-nocm). -/
theorem fibreComTrivial_of_gp3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3) :
    G0FibreSimple.FibreComTrivial :=
  fibreComTrivial_of_full (FS5NoCM.fibreComTrivialFull_of_leaves'' (r1r2fpFull_of r)
    (mobiusGlue_of_gp3 t gp) t.t27 t.t6 gp.cmOptimalEmbedding gp.x6KummerFibre r.r5count)

/-- **`GluePieces` from `GluePieces3` and the leaf bundles** (g0-assemble2). -/
theorem gluePieces_of_gluePieces3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3) :
    GluePieces where
  dimFinite := G0Split.dimFinite
  dimBaseChange := G0Split.dimBaseChange
  fibreSimple := G0FibreSimple.fibreSimple_of_leaves t
    (MulRigidity.mulIsogeny_of_mulEtale gp.mulEtale) G0FibreSimple.rigidityHom
    ⟨G0FibreSimple.finiteDescends_proof, fibreComTrivial_of_gp3 r t gp⟩
  productModelHeight := ZInQ.ProductHeight.productModelHeight_of_splits gp.productUnifSplits
    gp.productMetrizationOfProductUnif
  stableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine
    (ZInQ.HeightBC.g0_hodgeLine_iff.mpr (ZInQ.HeightBC.hodgeLineBaseChange_of_glue4
      gp.hodgeBCInjective gp.cotangentSpanBC gp.omegaBaseChange gp.uniformizationLiftAnalytic))
  productExists := G0Product.productExists
  reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3 r G0Split.dimFinite
  thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios
    (G0Split.FibreQM.fibreQMPeriod_main_rep r.r1r2 (mobiusGlue_of_gp3 t gp) gp.qmHauptmodul
      t.t35 t.t11a gp.qmClassNumberOne (gp.r1bFamily r.r1r2) (gp.periodMapGlue r.r1r2)
      gp.hauptmodulUnique gp.qmDenZeroCM3 gp.cPtsTransport)
    gp.thetaRatiosAlgebraic
  modularConstituent := modularConstituent_of_field t
    (G0ModField.fibreCoverExists_of_propTSAll' t.t5 gp.propTSAll gp.unramifiedConjugates)
    (G0ModField.KernelField.kernelFieldExists_of_split'' t.t6 r.r7a r.r6 t.t5 t.t27
      (fibreComTrivial_of_gp3 r t gp) gp.oMaximal gp.endTransport gp.conjIsogMaps)
    UnramTate.unramifiedSup_mf
    (G0AssembleMod.afterG7_of3 r t
      ⟨gp.burnsideAbsIrred, gp.r14Det, gp.g9Glue,
        G0Galois.g10Glue_of_conjTwist (G0Galois.conjTwistNontrivial_main t.t26 t.t35
          gp.artinTorsionSurj gp.homLinearLift gp.conjUniformization),
        G0Galois.g12Weight_of_senTwist gp.senTwist gp.finiteImageHT,
        G0Galois.detTate_of_leaves gp.t09SymmIsogenyExists gp.isogenyQuasiInverse
          gp.divisiblePoints t.t26,
        G0AssembleMod.resQFiniteIndex⟩
      (G0ModNewform.dirichletOfFinite_of_t17 t.t17) gp.carayolR17
      Swan.swanIndependent_proved Swan.swanIntegral_proved
      Swan.adaptedExists_proved gp.modelG3G6
      (G0AssembleMod.linkedTateData_of_local t.t7 gp.linkedTateLocal))
  heightCopies := G0HeightCopies.heightCopiesAgree

/-- **G0 after waves 26-27** (g0-assemble2): the leaf bundles (`ResearchLeaves3`: no `opaque`
placeholder) and `GluePieces3` imply `ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leavesR3 r t (gluePieces_of_gluePieces3 r t gp)

/-- The same with Leaves.lean's `ResearchLeaves` (which implies `ResearchLeaves3`). -/
theorem sixContactMin_of_leaves3' (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces3) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leaves3 (researchLeaves3_of r) t gp

end HSyn

end

#print axioms HSyn.gluePieces_of_gluePieces3
#print axioms HSyn.sixContactMin_of_leaves3
#print axioms HSyn.sixContactMin_of_leaves3'
#print axioms HSyn.researchLeaves3_of
