/-! ## leaf-fold6, part f20: leaf-fold5's statement with leafq-check's four reductions, T8 kept as a leaf

Task leaf-fold6, 2026-11-14. Everything above is leaf-fold5's chain (leaf-fold4's `Leaves4.lean` as the olean chain
LPrefix ... TailK, then leaf-fold5's TailL, TailM, TailN) and part f10 (leafq-check's `Fold.lean`, with its own
bundle names suffixed `Q`).

`sixContactMin_of_open6` is leaf-fold4's `sixContactMin_of_open4` applied to leaf-fold4's four bundles, each built
here from leaf-fold6's (as leaf-fold5's `sixContactMin_of_open5` does): every field of leaf-fold4 that changed is a
theorem whose type is the chain's own Prop, so Lean checks that the statements agree.

Changes against leaf-fold5's bundles:
* (a) leafq-check's four reductions of `OpenAddedLeaves5`:
  - `gammaStarGen` dropped: `LeafQCheck.gammaStarGen_proof`;
  - `valenceBoundGammaStar` → `valenceFormulaGammaStar`: `LeafQCheck.VB.valenceBound_of_formula`;
  - `cmDescends` → `stQM`: `PeriodMapH.LeafQCheck.cmDescends_of` with leaf-fold5's versions of its other inputs:
    `t11b := t11b_of_exists5 t.t11bExists` (leaf-fold5 weakened T11(b) to its existence half),
    `t5 := torsionStructure_ofK5 t.t5` (leaf-fold5 restated T5 over the kernel's Prop), `r1r2 := r.r1r2`;
  - `qmHauptmodul` → `qmHauptmodulBase3`: `LeafQCheck.HM.qmHauptmodul_of_base2 ∘ base2_of_base3` with `r.r4`,
    `gammaStarGen_proof` and the valence bound from `valenceFormulaGammaStar`.
* (b) T8 kept as a textbook leaf, over the kernel's own Prop `_root_.PkgI3.PoincareReducibility`
  (`ZInQKernel/HDecomp/Objects.lean`), transported to the chain's copy by `t8_ofK6`; leaf-fold5's
  `poincareComplement` (LEAF) and the glue `simpleImageIsogeny` are not fields. Glue: 1 (`ModelCoordinateResidue`).
  The other choice is `sixContactMin_of_open6_poincare` below (T8 from the kernel's
  `ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage`; glue 2).
* (c) Every field leaf-fold5 put on a kernel constant stays on it (`OpenResearchLeaves5` is reused unchanged). -/

noncomputable section

namespace HDec.HSyn

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **T8, the chain's copy, from the kernel's Prop** (same statement; the abelian varieties pass by leaf-fold4's
`toAbVarK4`/`ofAbVarK4`, as in leaf-fold5's `t8_of_simpleImage5`). -/
theorem t8_ofK6 (h : _root_.PkgI3.PoincareReducibility) : PkgI3.PoincareReducibility := by
  intro k _ _ A J hA f hf
  obtain ⟨Z, g, hg⟩ := h k (toAbVarK4 A) (toAbVarK4 J) hA f hf
  exact ⟨ofAbVarK4 Z, g, hg⟩

/-- **The textbook leaves still open** (leaf-fold6): leaf-fold5's `OpenTextbookLeaves5` with `poincareComplement`
replaced by T8 itself, `t8 : _root_.PkgI3.PoincareReducibility` (the kernel's Prop; goal (b): this keeps the glue
count at 1). The other 20 fields are leaf-fold5's, with the same types. -/
structure OpenTextbookLeaves6 : Prop where
  /-- neron-c, LEAF: every `K`-morphism of the generic fibres of two abelian schemes over a DVR extends
  (BLR §1.2 Prop. 8, surjective half). -/
  t3Surj : _root_.ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj.{0}
  /-- T4 = I2-Red, reduction is bijective on prime-to-`p` torsion. -/
  t4 : _root_.PkgI2.ReductionTorsionBijective.{0}
  t5 : _root_.PkgI2.TorsionStructure.{0}
  /-- av-b1, LEAF: Mumford §19 Thm 3 over an algebraically closed field. -/
  homFreeFiniteAlgClosed : _root_.ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed
  /-- av-b1, LEAF: Mumford §19 Thm 4 (consequence) over an algebraically closed field. -/
  charPolyIndepOfEllAlgClosed : _root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
  /-- T8 (I3.M3), Poincaré complete reducibility in the form used at E1, the kernel's Prop. -/
  t8 : _root_.PkgI3.PoincareReducibility
  t10 : _root_.T10Etale.T10_TateDuality
  homLatticeCorr : _root_.ZInQ.HomUnify.HomLatticeCorr
  /-- av-b2, LEAF: T11(b) without its uniqueness clause (Conrad 2006 §3; Milne 1986 §20). -/
  t11bExists : AVB2.T11bExists
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : _root_.PkgI4.EigenformTwist
  t27 : _root_.PkgI3.QMDichotomyYu
  t33 : _root_.LeafModCurves.JacobianExists ℚ
  /-- curves-g: `dim Jac X = genus` for curves over `ℚ` (Milne 1986 Prop. 2.1 with Serre duality). -/
  dimJacobianEqGenus : _root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus
  /-- curves-g: the genus of `K_N` is the genus of `Γ₁(N)` (Shimura 1971 §6.7 and Prop. 1.40). -/
  genusX1Field : _root_.ZInQ.Contrib.CurvesG.GenusX1Field
  t35 : _root_.ZInQ.LeafPush2.UniformizationExists
  /-- curves-g (A): a normal proper model of a function field over `ℚ(T)` (Stacks 0BXX). -/
  normalModelOfFunctionFieldQ : _root_.ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ
  /-- curves-g (B): a normal integral curve locally of finite type over `ℚ` is smooth. -/
  normalCurveSmoothQ : _root_.ZInQ.Contrib.CurvesG.NormalCurveSmoothQ
  /-- curves-g (C): constant field `ℚ` gives geometric connectedness (Stacks 0FD1). -/
  geomConnectedOfConstantFieldQ : _root_.ZInQ.Contrib.CurvesG.GeomConnectedOfConstantFieldQ
  x0Transitive : _root_.ZInQ.RLeaf.X0Transitive
  /-- neron-c, LEAF: a smooth separated quasi-compact `𝓞_L`-scheme with generic fibre `A_L` to which maps from
  smooth schemes extend (BLR §1.4 Thm 3, scheme level). -/
  neronSchemeExtensionExists : _root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists

/-- **The added leaves still open** (leaf-fold6): leaf-fold5's `OpenAddedLeaves5` with leafq-check's reductions:
`gammaStarGen` dropped (proved), `valenceBoundGammaStar` → `valenceFormulaGammaStar`, `cmDescends` → `stQM`,
`qmHauptmodul` → `qmHauptmodulBase3`. 20 fields. -/
structure OpenAddedLeaves6 : Prop where
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- leafq-check, LEAF?: the Hauptmodul property of the theta quotient on `Γ*` and its value `−16/27` at the
  order-2 point (the clauses at the discriminants `−4`, `−3` are proved). -/
  qmHauptmodulBase3 : LeafQCheck.HM.QMHauptmodulBase3
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  senTwist : G0Galois.SenTwist
  finiteImageHT : G0Galois.FiniteImageHT
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  x6ConicModel : X6Kummer.X6ConicModel
  y3Connected : TSHecke.Y3Connected
  qmAutCard : HeckeRest.QMAutCard
  alFixedPoints : HeckeRest.ALFixedPoints
  zariskiConnectedness : _root_.ZariskiConn.ZariskiConnectedness.{0}
  /-- leafq-check, LEAF: Shimura–Taniyama for QM surfaces with CM (`A ≅ A₀ ×_{ℚ̄} ℂ`). -/
  stQM : G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM
  /-- leafq-check, LEAF: the valence formula on `Γ*` (signature `(0;2,4,6)`) on finite sets of inequivalent
  points. -/
  valenceFormulaGammaStar : LeafQCheck.VB.ValenceFormulaGammaStar
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii
  /-- vert-witness, LEAF?: good reduction of the level-3 Shimura curve `Y₃` at `p > 324` with its universal
  family and Hecke automorphisms (Kottwitz 1992 §5; Morita 1981; Carayol 1986; Buzzard 1997). -/
  shimuraGoodReduction : VertWitness.ShimuraGoodReduction
  /-- model-glue, LEAF?: a morphism of proper smooth curves over `ℚ` bijective on `ℚ̄`-points is an
  isomorphism (Hartshorne II.6.7-6.9, III.10.7; EGA III 4.4.2). -/
  curveBijIso : ModelGlue.CurveBijIso

/-- **The glue still open** (leaf-fold6): model-glue's `ModelCoordinateResidue` only. -/
structure OpenGlue6 : Prop where
  /-- model-glue: a coordinate `ρ : 𝒴 → P¹` on the smooth model with transcendental residue at every point
  whose stalk is a DVR with maximal ideal `(p)` (the tame quotient `𝒴/Γ' ≅ P¹_{ℤ_(p)}`). -/
  modelCoordinateResidue : ModelGlue.ModelCoordinateResidue

/-- leaf-fold4's textbook bundle from leaf-fold6's (as leaf-fold5's `textbookLeaves4_of_open5`, with
`t8 := t8_ofK6 t.t8`). -/
theorem textbookLeaves4_of_open6 (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6) : OpenTextbookLeaves4 where
  t3 := t3_of_surj5 t.t3Surj
  t4 := reductionTorsionBijective_ofK5 t.t4
  t5 := torsionStructure_ofK5 t.t5
  t6 := t6_of_algClosed5 t.homFreeFiniteAlgClosed
  t7 := t7_of_algClosed5 t.charPolyIndepOfEllAlgClosed
  t8 := t8_ofK6 t.t8
  t9 := t9_of_leaves5 l.t09SymmIsogenyExists l.isogenyQuasiInverse
  t10 := t10_ofK5 t.t10
  homLatticeCorr := homLatticeCorr_ofK5 t.homLatticeCorr
  t11b := t11b_of_exists5 t.t11bExists
  t23 := t.t23
  t24 := eigenformTwist_ofK5 t.t24
  t27 := qmDichotomyYu_ofK5 t.t27
  t33 := jacobianExists_ofK5 t.t33
  t34 := t34_of_split5 t.dimJacobianEqGenus t.genusX1Field
  t35 := uniformizationExists_ofK5 t.t35
  t38 := t38_of_split5 t.normalModelOfFunctionFieldQ t.normalCurveSmoothQ t.geomConnectedOfConstantFieldQ
  x0Transitive := t.x0Transitive
  t41 := t41_of_extension5 t.neronSchemeExtensionExists

/-- **`CMDescends` from Shimura–Taniyama** (leafq-check's `cmDescends_of`, with leaf-fold5's T11(b) and T5). -/
theorem cmDescends_of6 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6) :
    G0Split.FibreQM.PeriodMapH.CMDescends :=
  G0Split.FibreQM.PeriodMapH.LeafQCheck.cmDescends_of l.stQM (t11b_of_exists5 t.t11bExists)
    (G0Split.FibreQM.PeriodMapH.LeafQCheck.torsionDescends_of_t5 (torsionStructure_ofK5 t.t5)) r.r1r2

/-- **`QMHauptmodul` from `QMHauptmodulBase3`** (leafq-check's `base2_of_base3` and `qmHauptmodul_of_base2`:
R4, `GammaStarGen` (proved) and the valence bound (from the valence formula)). -/
theorem qmHauptmodul_of6 (r : OpenResearchLeaves5) (l : OpenAddedLeaves6) : PkgI1.QMHauptmodul :=
  LeafQCheck.HM.qmHauptmodul_of_base2
    (LeafQCheck.HM.base2_of_base3 r.r4 LeafQCheck.gammaStarGen_proof
      (LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar) l.qmHauptmodulBase3)

/-- leaf-fold4's added-leaves bundle from leaf-fold6's. -/
theorem addedLeaves4_of_open6 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6) :
    OpenAddedLeaves4 where
  cmOptimalEmbedding := l.cmOptimalEmbedding
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmHauptmodul := qmHauptmodul_of6 r l
  qmClassNumberOne := l.qmClassNumberOne
  senTwist := l.senTwist
  finiteImageHT := l.finiteImageHT
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  isogenyQuasiInverse := l.isogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := l.qmAutCard
  serreRigidity3 := serreRigidity3_of_T35_5 (uniformizationExists_ofK5 t.t35) (homLatticeCorr_ofK5 t.homLatticeCorr)
  alFixedPoints := l.alFixedPoints
  zariskiConnectedness := l.zariskiConnectedness
  cmDescends := cmDescends_of6 r t l
  gammaStarGen := LeafQCheck.gammaStarGen_proof
  valenceBoundGammaStar := LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar
  egaIV_8_8_2_ii := l.egaIV_8_8_2_ii
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := l.egaIV_17_7_8_ii

/-- leaf-fold4's glue bundle from leaf-fold6's: `HeckeVertWitness` from leaves and `ModelCoordinateResidue`
(leaf-fold5's `heckeVertWitness_of_leaves5`). -/
theorem glue4_of_open6 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6)
    (g : OpenGlue6) : OpenGlue4 where
  heckeVertWitness := heckeVertWitness_of_leaves5 l.shimuraGoodReduction r.r1r2 (torsionStructure_ofK5 t.t5)
    g.modelCoordinateResidue l.curveBijIso

/-- **G0 with only the open leaves and the open glue** (leaf-fold6; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from
* `OpenResearchLeaves5`: 26 research-level fields (leaf-fold5's bundle, unchanged; nine on the kernel's Props);
* `OpenTextbookLeaves6`: 21 textbook fields (T8 kept, on the kernel's Prop);
* `OpenAddedLeaves6`: 20 added leaves;
* `OpenGlue6`: 1 glue Prop (`ModelCoordinateResidue`).
The table of every field is `docs/research/leaf-fold6.md` §2. -/
theorem sixContactMin_of_open6 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves6)
    (l : OpenAddedLeaves6) (g : OpenGlue6) : ZInQ.SixContactMin :=
  sixContactMin_of_open4 (researchLeaves2_of_open5 r) (textbookLeaves4_of_open6 t l) (addedLeaves4_of_open6 r t l)
    (glue4_of_open6 r t l g)

/-- **The other choice for T8** (goal (b)): leaf-fold5's textbook bundle (with `poincareComplement`) and leaf-fold5's
glue bundle (with `simpleImageIsogeny`): 26 + 21 + 20 + 2 = 69 fields, glue 2. T8 is the kernel's
`ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage`. -/
theorem sixContactMin_of_open6_poincare (r : OpenResearchLeaves5) (t : OpenTextbookLeaves5)
    (l : OpenAddedLeaves6) (g : OpenGlue5) : ZInQ.SixContactMin :=
  sixContactMin_of_open6 r
    { t3Surj := t.t3Surj, t4 := t.t4, t5 := t.t5, homFreeFiniteAlgClosed := t.homFreeFiniteAlgClosed,
      charPolyIndepOfEllAlgClosed := t.charPolyIndepOfEllAlgClosed,
      t8 := _root_.ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage t.poincareComplement g.simpleImageIsogeny,
      t10 := t.t10, homLatticeCorr := t.homLatticeCorr, t11bExists := t.t11bExists, t23 := t.t23, t24 := t.t24,
      t27 := t.t27, t33 := t.t33, dimJacobianEqGenus := t.dimJacobianEqGenus, genusX1Field := t.genusX1Field,
      t35 := t.t35, normalModelOfFunctionFieldQ := t.normalModelOfFunctionFieldQ,
      normalCurveSmoothQ := t.normalCurveSmoothQ, geomConnectedOfConstantFieldQ := t.geomConnectedOfConstantFieldQ,
      x0Transitive := t.x0Transitive, neronSchemeExtensionExists := t.neronSchemeExtensionExists }
    l ⟨g.modelCoordinateResidue⟩

/-- leaf-fold5's added-leaves bundle from leaf-fold6's: the four fields leafq-check replaced are theorems from the
new fields (and `r4`, `r1r2`, T5, T11(b)); the other 17 are the same fields. -/
theorem addedLeaves5_of_open6 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6) :
    OpenAddedLeaves5 where
  cmOptimalEmbedding := l.cmOptimalEmbedding
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmHauptmodul := qmHauptmodul_of6 r l
  qmClassNumberOne := l.qmClassNumberOne
  senTwist := l.senTwist
  finiteImageHT := l.finiteImageHT
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  isogenyQuasiInverse := l.isogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := l.qmAutCard
  alFixedPoints := l.alFixedPoints
  zariskiConnectedness := l.zariskiConnectedness
  cmDescends := cmDescends_of6 r t l
  gammaStarGen := LeafQCheck.gammaStarGen_proof
  valenceBoundGammaStar := LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar
  egaIV_8_8_2_ii := l.egaIV_8_8_2_ii
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := l.egaIV_17_7_8_ii
  shimuraGoodReduction := l.shimuraGoodReduction
  curveBijIso := l.curveBijIso

end HDec.HSyn

end

example : ∀ (_ : HDec.HSyn.OpenResearchLeaves5) (_ : HDec.HSyn.OpenTextbookLeaves6)
    (_ : HDec.HSyn.OpenAddedLeaves6) (_ : HDec.HSyn.OpenGlue6), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_open6

example : ∀ (_ : HDec.HSyn.OpenResearchLeaves5) (_ : HDec.HSyn.OpenTextbookLeaves5)
    (_ : HDec.HSyn.OpenAddedLeaves6) (_ : HDec.HSyn.OpenGlue5), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_open6_poincare

#print axioms HDec.HSyn.t8_ofK6
#print axioms HDec.HSyn.cmDescends_of6
#print axioms HDec.HSyn.qmHauptmodul_of6
#print axioms HDec.HSyn.textbookLeaves4_of_open6
#print axioms HDec.HSyn.addedLeaves4_of_open6
#print axioms HDec.HSyn.glue4_of_open6
#print axioms HDec.HSyn.addedLeaves5_of_open6
#print axioms HDec.HSyn.sixContactMin_of_open6
#print axioms HDec.HSyn.sixContactMin_of_open6_poincare
