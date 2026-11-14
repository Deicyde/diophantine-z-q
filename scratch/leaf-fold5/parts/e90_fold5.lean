/-! ## leaf-fold5: the results since leaf-fold4, folded into the statement of what remains open

Task leaf-fold5, 2026-11-14. Everything above this part is leaf-fold4's `Leaves4.lean` (olean chain LPrefix ...
TailK, unchanged), then part e10 (vert-witness's `VertMain.lean.part` and model-glue's six parts, in
`namespace HDec`), part e20 (av-b2's `AVB2Main.lean`, namespace `AVB2`) and part e30 (the chain's textbook fields
from the kernel's av-b1, curves-g and neron-c theorems). The kernel modules `Contrib.SmoothFibre.Basic`,
`Contrib.AVB2.SerreLemma`, `Contrib.AVB1.{AlgClosed,Poincare}`, `Contrib.CurvesG.{CurveSplit,GenusSplit}` and
`Contrib.NeronC.{NMPInjective,NeronGroup}` are imported.

`sixContactMin_of_open5` is leaf-fold4's `sixContactMin_of_open4` applied to leaf-fold4's four bundles, each
built here from leaf-fold5's: every field of leaf-fold4 that changed is a theorem below whose type is the chain's
own Prop, so Lean checks that the statements agree. -/

noncomputable section

namespace HSyn

open CategoryTheory AlgebraicGeometry

/-! ### (a) `HeckeVertWitness` from good reduction of `Y₃` (vert-witness, smooth-fibre, model-glue) -/

/-- **`HeckeVertWitness` from leaves and one glue Prop** (model-glue's `ModelGlue.heckeVertWitness_of_curveBijIso`,
part e10, with `SmoothFibreReduced` the kernel's theorem `ZInQ.SmoothFibre.smoothFibreReduced`): the leaf
`ShimuraGoodReduction` (a smooth proper model of `Y₃` over `ℤ_(p)` for `p > 324`), R1fp/R1hecke/R2fp (the bundle
field `r1r2`), T5, the textbook leaf `CurveBijIso` and the glue `ModelCoordinateResidue` (the tame quotient
`𝒴/Γ' ≅ P¹_{ℤ_(p)}`). -/
theorem heckeVertWitness_of_leaves5 (hL : VertWitness.ShimuraGoodReduction) (h : LeafAdopt.R1R2fpRep)
    (hT : PkgI2.TorsionStructure.{0}) (hD : ModelGlue.ModelCoordinateResidue)
    (hC : ModelGlue.CurveBijIso) : HeckeRestNV.HeckeVertWitness :=
  ModelGlue.heckeVertWitness_of_curveBijIso hL (LeafAdopt.R1R2fp_of_rep h)
    (ObjBridge.torsionStructure_iff.mpr hT) hD hC

/-! ### (b) av-b2: T9 and Serre's lemma proved from fields already present; T11(b) from its existence half -/

/-- **T9 from two existing fields** (av-b2's `AVB2.t9_of_leaves3`, part e20). -/
theorem t9_of_leaves5 (h9 : WeilPairing.T09_SymmIsogenyExists) (hQ : WeilPairing.IsogenyQuasiInverse) :
    LeafPush.T09_WeilPairing.{0} :=
  AVB2.t9_of_leaves3 h9 hQ

/-- **Serre's lemma at level 3 from T35 and `HomLatticeCorr`** (av-b2's `AVB2.serreRigidity3_of_T35`). -/
theorem serreRigidity3_of_T35_5 (hU : ZInQ.LeafPush2.UniformizationExists) (hC : HomUnify.HomLatticeCorr) :
    HeckeRest.SerreRigidity3 :=
  AVB2.serreRigidity3_of_T35 hU hC

/-- **T11(b) from its existence half** (av-b2's `AVB2.t11b_of_exists`; uniqueness is proved). -/
theorem t11b_of_exists5 (h : AVB2.T11bExists) : ZInQ.LeafPush2.T11b_Rigidity :=
  AVB2.t11b_of_exists h

/-! ### The open statements -/

/-- **The textbook leaves still open** (leaf-fold5): `OpenTextbookLeaves4` with
* `t3` (T3) replaced by its surjective half `NeronMappingAbelianSchemeSurj` (neron-c);
* `t6`, `t7` (T6, T7) replaced by their forms over algebraically closed fields (av-b1; Mumford §19 Thms 3, 4);
* `t8` (T8) replaced by `PoincareComplement` (av-b1; with the glue `SimpleImageIsogeny`, in `OpenGlue5`);
* `t9` (T9) dropped (proved from `t09SymmIsogenyExists`, `isogenyQuasiInverse`; av-b2);
* `t11b` (T11(b)) replaced by its existence half `T11bExists` (av-b2);
* `t34` (T34) replaced by its two halves `DimJacobianEqGenus`, `GenusX1Field` (curves-g);
* `t38` (T38) replaced by curves-g's three statements (A), (B), (C) (its rational-point clause is proved);
* `t41` (T41) replaced by `NeronSchemeExtensionExists` (neron-c; the group law is proved). -/
structure OpenTextbookLeaves5 : Prop where
  /-- neron-c, LEAF: every `K`-morphism of the generic fibres of two abelian schemes over a DVR extends
  (BLR §1.2 Prop. 8, surjective half). -/
  t3Surj : _root_.ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj.{0}
  /-- T4 = I2-Red, reduction is bijective on prime-to-`p` torsion. -/
  t4 : PkgI2.ReductionTorsionBijective.{0}
  t5 : PkgI2.TorsionStructure.{0}
  /-- av-b1, LEAF: Mumford §19 Thm 3 over an algebraically closed field. -/
  homFreeFiniteAlgClosed : _root_.ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed
  /-- av-b1, LEAF: Mumford §19 Thm 4 (consequence) over an algebraically closed field. -/
  charPolyIndepOfEllAlgClosed : _root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
  /-- av-b1, LEAF: Poincaré's complement theorem (Milne 1986 Prop. 12.1; Mumford §19 Thm 1), weakened. -/
  poincareComplement : _root_.ZInQ.Contrib.AVB1.PoincareComplement
  t10 : T10Etale.T10_TateDuality
  homLatticeCorr : HomUnify.HomLatticeCorr
  /-- av-b2, LEAF: T11(b) without its uniqueness clause (Conrad 2006 §3; Milne 1986 §20). -/
  t11bExists : AVB2.T11bExists
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t27 : PkgI3.QMDichotomyYu
  t33 : LeafModCurves.JacobianExists ℚ
  /-- curves-g: `dim Jac X = genus` for curves over `ℚ` (Milne 1986 Prop. 2.1 with Serre duality). -/
  dimJacobianEqGenus : _root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus
  /-- curves-g: the genus of `K_N` is the genus of `Γ₁(N)` (Shimura 1971 §6.7 and Prop. 1.40). -/
  genusX1Field : _root_.ZInQ.Contrib.CurvesG.GenusX1Field
  t35 : ZInQ.LeafPush2.UniformizationExists
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

/-- **The added leaves still open** (leaf-fold5): `OpenAddedLeaves4` without `serreRigidity3` (proved from
T35 and `HomLatticeCorr`, av-b2), with vert-witness's `ShimuraGoodReduction` and model-glue's `CurveBijIso`. -/
structure OpenAddedLeaves5 : Prop where
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmHauptmodul : PkgI1.QMHauptmodul
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
  cmDescends : G0Split.FibreQM.PeriodMapH.CMDescends
  gammaStarGen : G0Split.FibreQM.PeriodGlue.GammaStarGen
  valenceBoundGammaStar : G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii
  /-- vert-witness, LEAF: good reduction of the level-3 Shimura curve `Y₃` at `p > 324` with its universal
  family and Hecke automorphisms (Kottwitz 1992 §5; Morita 1981; Carayol 1986; Buzzard 1997). -/
  shimuraGoodReduction : VertWitness.ShimuraGoodReduction
  /-- model-glue, LEAF (textbook): a morphism of proper smooth curves over `ℚ` bijective on `ℚ̄`-points is an
  isomorphism (Hartshorne II.6.7-6.9, III.10.7; EGA III 4.4.2). -/
  curveBijIso : ModelGlue.CurveBijIso

/-- **The glue still open** (leaf-fold5). `HeckeVertWitness` (leaf-fold4's one glue Prop) is now a theorem from
leaves and `modelCoordinateResidue`; av-b1's `SimpleImageIsogeny` enters with T8's reduction. -/
structure OpenGlue5 : Prop where
  /-- model-glue: a coordinate `ρ : 𝒴 → P¹` on the smooth model with transcendental residue at every point
  whose stalk is a DVR with maximal ideal `(p)` (the tame quotient `𝒴/Γ' ≅ P¹_{ℤ_(p)}`). -/
  modelCoordinateResidue : ModelGlue.ModelCoordinateResidue
  /-- av-b1: a nonzero homomorphism out of a simple abelian variety is an isogeny onto its image. -/
  simpleImageIsogeny : _root_.ZInQ.Contrib.AVB1.SimpleImageIsogeny

/-- leaf-fold4's textbook bundle from leaf-fold5's. -/
theorem textbookLeaves4_of_open5 (t : OpenTextbookLeaves5) (l : OpenAddedLeaves5) (g : OpenGlue5) :
    OpenTextbookLeaves4 where
  t3 := t3_of_surj5 t.t3Surj
  t4 := t.t4
  t5 := t.t5
  t6 := t6_of_algClosed5 t.homFreeFiniteAlgClosed
  t7 := t7_of_algClosed5 t.charPolyIndepOfEllAlgClosed
  t8 := t8_of_simpleImage5 t.poincareComplement g.simpleImageIsogeny
  t9 := t9_of_leaves5 l.t09SymmIsogenyExists l.isogenyQuasiInverse
  t10 := t.t10
  homLatticeCorr := t.homLatticeCorr
  t11b := t11b_of_exists5 t.t11bExists
  t23 := t.t23
  t24 := t.t24
  t27 := t.t27
  t33 := t.t33
  t34 := t34_of_split5 t.dimJacobianEqGenus t.genusX1Field
  t35 := t.t35
  t38 := t38_of_split5 t.normalModelOfFunctionFieldQ t.normalCurveSmoothQ t.geomConnectedOfConstantFieldQ
  x0Transitive := t.x0Transitive
  t41 := t41_of_extension5 t.neronSchemeExtensionExists

/-- leaf-fold4's added-leaves bundle from leaf-fold5's (`serreRigidity3` from T35 and `HomLatticeCorr`). -/
theorem addedLeaves4_of_open5 (t : OpenTextbookLeaves5) (l : OpenAddedLeaves5) : OpenAddedLeaves4 where
  cmOptimalEmbedding := l.cmOptimalEmbedding
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmHauptmodul := l.qmHauptmodul
  qmClassNumberOne := l.qmClassNumberOne
  senTwist := l.senTwist
  finiteImageHT := l.finiteImageHT
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  isogenyQuasiInverse := l.isogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := l.qmAutCard
  serreRigidity3 := serreRigidity3_of_T35_5 t.t35 t.homLatticeCorr
  alFixedPoints := l.alFixedPoints
  zariskiConnectedness := l.zariskiConnectedness
  cmDescends := l.cmDescends
  gammaStarGen := l.gammaStarGen
  valenceBoundGammaStar := l.valenceBoundGammaStar
  egaIV_8_8_2_ii := l.egaIV_8_8_2_ii
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := l.egaIV_17_7_8_ii

/-- leaf-fold4's glue bundle from leaf-fold5's: `HeckeVertWitness` from leaves and `ModelCoordinateResidue`. -/
theorem glue4_of_open5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves5) (l : OpenAddedLeaves5)
    (g : OpenGlue5) : OpenGlue4 where
  heckeVertWitness := heckeVertWitness_of_leaves5 l.shimuraGoodReduction r.r1r2 t.t5
    g.modelCoordinateResidue l.curveBijIso

/-- **G0 with only the open leaves and the open glue** (leaf-fold5; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from
* `OpenResearchLeaves2`: 26 research-level fields (unchanged);
* `OpenTextbookLeaves5`: 21 textbook fields;
* `OpenAddedLeaves5`: 21 added leaves;
* `OpenGlue5`: 2 glue Props (`ModelCoordinateResidue`, `SimpleImageIsogeny`).
The table of every field is `docs/research/leaf-fold5.md` §2. -/
theorem sixContactMin_of_open5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves5)
    (l : OpenAddedLeaves5) (g : OpenGlue5) : ZInQ.SixContactMin :=
  sixContactMin_of_open4 r (textbookLeaves4_of_open5 t l g) (addedLeaves4_of_open5 t l)
    (glue4_of_open5 r t l g)

end HSyn

end

#print axioms HSyn.heckeVertWitness_of_leaves5
#print axioms HSyn.t9_of_leaves5
#print axioms HSyn.serreRigidity3_of_T35_5
#print axioms HSyn.t11b_of_exists5
#print axioms HSyn.t6_of_algClosed5
#print axioms HSyn.t7_of_algClosed5
#print axioms HSyn.t8_of_simpleImage5
#print axioms HSyn.t38_of_split5
#print axioms HSyn.t34_of_split5
#print axioms HSyn.t3_of_surj5
#print axioms HSyn.t41_of_extension5
#print axioms HSyn.textbookLeaves4_of_open5
#print axioms HSyn.addedLeaves4_of_open5
#print axioms HSyn.glue4_of_open5
#print axioms HSyn.sixContactMin_of_open5
