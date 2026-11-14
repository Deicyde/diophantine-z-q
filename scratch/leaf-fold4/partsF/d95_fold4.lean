/-! ## leaf-fold4: the results since leaf-fold3, folded into the statement of what remains open

Task leaf-fold4, 2026-11-13. Everything above this part is leaf-fold3's `Leaves3.lean` (part c80 regenerated
from hecke-rest's final `HeckeRestAll.lean`, which proves `ChartProper` and `ChartQuasiFinite`) and part
c90 (`mk_periodglue.py`: period-map's parts and period-glue's six files). The kernel modules
`ZInQKernel.Contrib.ZariskiConn.Basic` (zariski-conn) and `ZInQKernel.Contrib.SpreadOut.NumberField`
(spread-out) and the root module `LF4T5` (t5-torsion's `T5Full.lean`, verbatim) are imported.

`sixContactMin_of_open4` is proved by building leaf-fold3's four bundles from the new ones and applying
`sixContactMin_of_open3`; each field of an old bundle that is no longer a hypothesis is a theorem below,
whose type is this file's own Prop, so Lean checks that the statements agree. -/

noncomputable section

namespace HSyn

open CategoryTheory AlgebraicGeometry G0Split

/-! ### Glue closed since leaf-fold3 -/

/-- **`ChartProper` proved** (hecke-rest, `HeckeRestCurve.chartProper`, part c80; Mathlib only). -/
theorem chartProper_proved4 : HeckeRestCurve.ChartProper := HeckeRestCurve.chartProper

/-- **`ChartQuasiFinite` proved** (hecke-rest, `HeckeRestCurve.chartQuasiFinite_of_proper`, part c80). -/
theorem chartQuasiFinite_proved4 : HeckeRestCurve.ChartQuasiFinite :=
  HeckeRestCurve.chartQuasiFinite_of_proper HeckeRestCurve.chartProper

/-- **`HauptmodulUnique` proved** (period-map's `hauptmodulUnique_of'` with period-glue's
`s8Nonzero_proof` (a certified theta evaluation) and `sphereFactorAffine_proof`; part c90). -/
theorem hauptmodulUnique_proved4 : G0Split.FibreQM.HauptmodulUnique :=
  G0Split.FibreQM.PeriodMap.hauptmodulUnique_of' G0Split.FibreQM.PeriodGlue.s8Nonzero_proof
    G0Split.FibreQM.PeriodGlue.sphereFactorAffine_proof

/-- **`AutOInnerFinite` from the kernel** (mobius-glue's proof, `ZInQKernel/Contrib/Mobius/Glue.lean`,
`LeafQM.AV.Pin.autOInnerFinite`, imported). The kernel's statement is over the kernel's `LeafQM.O`, this
file's over its copy; the two definitions have the same body, and Lean accepts the term. -/
theorem autOInnerFinite_proved4 : G0Split.FibreQM.PeriodGlue.AutOInnerFinite :=
  _root_.LeafQM.AV.Pin.autOInnerFinite

/-- **Skolem–Noether** (the kernel's `TSkolemKW.leafSkolemNoether`,
`ZInQKernel/HDecomp/Textbook/SkolemNoether.lean`, imported; same remark). -/
theorem leafSkolemNoether_proved4 : GlueDescent.LeafSkolemNoether :=
  _root_.TSkolemKW.leafSkolemNoether

/-- **period-glue's `T11aRiemannHom` from hom-unify's `HomLatticeCorr`** (both clauses at `g = h`,
`K = ℂ`, `σ = id`; proved). -/
theorem t11aRiemannHom_of_corr4 (h : HomUnify.HomLatticeCorr) :
    G0Split.FibreQM.PeriodGlue.T11aRiemannHom :=
  fun A A' g Λ Λ' Φ Φ' hA hA' hU hU' =>
    ⟨fun M hM => h.2 A A' g g Λ Λ' Φ Φ' hA hA' hU hU' M hM,
     fun f => h.1 ℂ A A' (RingHom.id ℂ) g g Λ Λ' Φ Φ' hA hA' hU hU' f⟩

/-- **`PeriodMapGlue` at the leaf's own triple from leaves** (period-map's `periodMapGlue_own` with
period-glue's pieces, as in period-glue's `fibreQMPeriod_periodGlue`; part c90). Inputs: R1fp, R1hecke, R2fp
(the bundle `R1R2fpRep`), T5 (`TorsionStructure`), `T11aRiemannHom` (from `HomLatticeCorr`), the leaf
candidate `CMDescends`; `AutOInnerFinite` and Skolem–Noether are kernel theorems. -/
theorem periodMapGlue_of_leaves4 (h : LeafAdopt.R1R2fpRep) (hT : PkgI2.TorsionStructure.{0})
    (hC : HomUnify.HomLatticeCorr) (hD : G0Split.FibreQM.PeriodMapH.CMDescends) :
    G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h)) :=
  have hHom := t11aRiemannHom_of_corr4 hC
  have hPT := G0Split.FibreQM.PeriodGlue.piTwistC_of _ _ _
    (G0Split.FibreQM.own_spec (LeafAdopt.R1R2fp_of_rep h)).1
    (G0Split.FibreQM.own_spec (LeafAdopt.R1R2fp_of_rep h)).2.2
    (G0Split.FibreQM.PeriodGlue.twistOrbitFinite_of' _ _
      (G0Split.FibreQM.own_spec (LeafAdopt.R1R2fp_of_rep h)).2.1
      (ObjBridge.torsionStructure_iff.mpr hT) autOInnerFinite_proved4)
    (G0Split.FibreQM.PeriodGlue.fibreTransferC_proof _ _)
  G0Split.FibreQM.PeriodMapH.periodMapGlue_own _
    G0Split.FibreQM.PeriodGlue.baseChangeClassUnique_proof hPT
    (G0Split.FibreQM.PeriodGlue.qmTwistLattice_of' hHom leafSkolemNoether_proved4)
    (G0Split.FibreQM.PeriodMapH.piCMC_of _ _ _
      (G0Split.FibreQM.own_spec (LeafAdopt.R1R2fp_of_rep h)).1
      (G0Split.FibreQM.own_spec (LeafAdopt.R1R2fp_of_rep h)).2.2
      G0Split.FibreQM.PeriodGlue.baseChangeClassUnique_proof hPT hD)
    (G0Split.FibreQM.PeriodMapH.cmFixedHasCM_of
      (G0Split.FibreQM.PeriodGlue.t11aRiemannEnd_of_hom hHom))

/-- **`QMDenZeroCM3` from leaves** (period-map's `qmDenZeroCM3_of''` with period-glue's `s8Nonzero_proof`
and `s8WeightExact_of`; part c90): Igusa's `ThetaModularity` (R4), the leaf candidates `GammaStarGen`
and `ValenceBoundGammaStar`. -/
theorem qmDenZeroCM3_of_leaves4 (hTM : PkgI1.ThetaModularity)
    (hG : G0Split.FibreQM.PeriodGlue.GammaStarGen)
    (hV : G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar) : G0Split.FibreQM.QMDenZeroCM3 :=
  G0Split.FibreQM.PeriodMap.qmDenZeroCM3_of'' G0Split.FibreQM.PeriodGlue.s8Nonzero_proof
    (G0Split.FibreQM.PeriodGlue.s8WeightExact_of hTM hG) hV

/-- **`ProperSmoothGenConnected` from Zariski's connectedness theorem** (zariski-conn,
`ZariskiConn.properSmoothGenConnected_of_zariskiConnectedness`, `ZInQKernel/Contrib/ZariskiConn/Basic.lean`,
imported). The kernel's `ZariskiConn.ProperSmoothGenConnected` is a verbatim copy of this file's
`FrobPiecesNeron.ProperSmoothGenConnected` over Mathlib definitions only; Lean accepts the term. -/
theorem properSmoothGenConnected_of_zariski4 (hZ : _root_.ZariskiConn.ZariskiConnectedness.{0}) :
    FrobPiecesNeron.ProperSmoothGenConnected :=
  _root_.ZariskiConn.properSmoothGenConnected_of_zariskiConnectedness hZ

/-- The kernel's abelian variety with the same underlying scheme (as leaf-fold2's `toAbVarK`, for this
file's `PkgI3.AbVar`). -/
def toAbVarK4 {L : Type} [Field L] (B : PkgI3.AbVar L) : _root_.PkgI3.AbVar L := ⟨B.X⟩

/-- **N1-g1 `AbVarSpreadsOut` from the three EGA IV leaves** (spread-out,
`ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega`, `ZInQKernel/Contrib/SpreadOut/NumberField.lean`,
imported; its conclusion is the body of `AbVarSpreadsOut` for the kernel's `PkgI3.AbVar`, applied to
`toAbVarK4 B`, which has the same scheme `B.X`). -/
theorem abVarSpreadsOut_of_ega4 (h882 : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii)
    (hpr : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii)
    (hsm : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii) : FrobPiecesNeron.AbVarSpreadsOut :=
  fun L _ _ B => _root_.ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega h882 hpr hsm L (toAbVarK4 B)

/-! ### T26 from T5 (t5-torsion's `tateModuleFree_of_torsionStructure`, module `LF4T5`) -/

/-- This file's abelian variety with the same scheme as a kernel one. -/
def ofAbVarK4 {L : Type} [Field L] (B : _root_.PkgI3.AbVar L) : PkgI3.AbVar L := ⟨B.X⟩

/-- **T5 for the kernel's objects from T5 for this file's** (the two `TorsionStructure`s are verbatim
copies; only the class `IsAbelianVariety` is transported). -/
theorem torsionStructureK_of4 (h : PkgI2.TorsionStructure.{0}) : _root_.PkgI2.TorsionStructure.{0} := by
  intro K _ A hA g n hg hn hnK
  haveI : PkgI2.IsAbelianVariety A := ⟨hA.proper, hA.smooth, hA.geomIntegral⟩
  exact h K A g n hg hn hnK

/-- **T26 (I3.M0, `TateModuleFree`) from T5** (t5-torsion's
`T5Torsion.TateFree.tateModuleFree_of_torsionStructure`, over the kernel's objects, applied to `toAbVarK4 A`). -/
theorem tateModuleFree_of_t5' (h : PkgI2.TorsionStructure.{0}) : PkgI3.TateModuleFree :=
  fun k _ A ℓ _ hℓ =>
    _root_.T5Torsion.TateFree.tateModuleFree_of_torsionStructure (torsionStructureK_of4 h) k
      (toAbVarK4 A) ℓ hℓ

/-! ### The open statements -/

/-- **The textbook leaves still open** (leaf-fold4): `OpenTextbookLeaves3` without `t26` (T26 = I3.M0,
now a theorem from T5, `tateModuleFree_of_t5'`). -/
structure OpenTextbookLeaves4 : Prop where
  /-- T3 = I2-NMP, Néron mapping property of abelian schemes (BLR §1.2). -/
  t3 : PkgI2.NeronMappingAbelianScheme.{0}
  /-- T4 = I2-Red, reduction is bijective on prime-to-`p` torsion. -/
  t4 : PkgI2.ReductionTorsionBijective.{0}
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : LeafPush.T09_WeilPairing.{0}
  t10 : T10Etale.T10_TateDuality
  /-- hom-unify: analytic representation of homomorphisms (replaces T11(a) and `HomLinearLift`). -/
  homLatticeCorr : HomUnify.HomLatticeCorr
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t27 : PkgI3.QMDichotomyYu
  t33 : LeafModCurves.JacobianExists ℚ
  t34 : LeafModCurves.DimJ1Genus
  t35 : ZInQ.LeafPush2.UniformizationExists
  t38 : X1Belyi.CurveOfFunctionFieldQ
  /-- T40; the kernel derives it from `X0Transitive` (t40-igusa), not importable here (Tau Ceti clash). -/
  t40 : X1Belyi.X1RationalCusp
  t41 : ZInQ.H5Neron.NeronModelExists

/-- **The added leaves still open** (leaf-fold4): `OpenAddedLeaves3` with
* `qmDenZeroCM3` (LEAF?) replaced by period-glue's leaf candidates `GammaStarGen` and
  `ValenceBoundGammaStar` (with R4, `qmDenZeroCM3_of_leaves4`);
* `properSmoothGenConnected` (LEAF?) replaced by Zariski's connectedness theorem in its published form
  (zariski-conn);
* new: period-map's leaf candidate `CMDescends` (for `PeriodMapGlue`) and spread-out's three EGA IV
  leaves (for `AbVarSpreadsOut`). -/
structure OpenAddedLeaves4 : Prop where
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmHauptmodul : PkgI1.QMHauptmodul
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  senTwist : G0Galois.SenTwist
  finiteImageHT : G0Galois.FiniteImageHT
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  divisiblePoints : WeilPairing.DivisiblePoints
  x6ConicModel : X6Kummer.X6ConicModel
  y3Connected : TSHecke.Y3Connected
  qmAutCard : HeckeRest.QMAutCard
  serreRigidity3 : HeckeRest.SerreRigidity3
  alFixedPoints : HeckeRest.ALFixedPoints
  /-- zariski-conn, LEAF: Zariski's connectedness theorem (EGA III₁ 4.3.1 with 4.3.4). -/
  zariskiConnectedness : _root_.ZariskiConn.ZariskiConnectedness.{0}
  /-- period-map, LEAF?: a QM pair over `ℂ` with CM descends (Shimura; for `PeriodMapGlue`). -/
  cmDescends : G0Split.FibreQM.PeriodMapH.CMDescends
  /-- period-glue, LEAF?: `Γ*` is generated by `ι(1+i+j)`, `ι((j−3)/2)` and `ℚ^×`. -/
  gammaStarGen : G0Split.FibreQM.PeriodGlue.GammaStarGen
  /-- period-map, LEAF?: the valence bound for weight-8 forms on `Γ*`. -/
  valenceBoundGammaStar : G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar
  /-- spread-out, LEAF: EGA IV₃ 8.8.2 (ii) (descent of finitely presented schemes to a stage of a limit). -/
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  /-- spread-out, LEAF: EGA IV₃ 8.10.5 (xii) (properness descends). -/
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- spread-out, LEAF: EGA IV₄ 17.7.8 (ii) (smoothness descends). -/
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii

/-- **The glue still open** (leaf-fold4): of leaf-fold3's six fields, `chartProper`, `chartQuasiFinite`
(hecke-rest), `hauptmodulUnique` (period-glue) are proved, `periodMapGlue` (period-glue) and
`abVarSpreadsOut` (spread-out) rest on leaves. -/
structure OpenGlue4 : Prop where
  /-- hecke-rest: one vertical prime above `p > 324` unramified in the Hecke cover (equivalent to
  Lemma NV, `HeckeNoVertRam`). -/
  heckeVertWitness : HeckeRestNV.HeckeVertWitness

/-- leaf-fold3's textbook bundle from leaf-fold4's (T26 from T5). -/
theorem textbookLeaves3_of_open4 (t : OpenTextbookLeaves4) : OpenTextbookLeaves3 where
  t3 := t.t3
  t4 := t.t4
  t5 := t.t5
  t6 := t.t6
  t7 := t.t7
  t8 := t.t8
  t9 := t.t9
  t10 := t.t10
  homLatticeCorr := t.homLatticeCorr
  t11b := t.t11b
  t23 := t.t23
  t24 := t.t24
  t26 := tateModuleFree_of_t5' t.t5
  t27 := t.t27
  t33 := t.t33
  t34 := t.t34
  t35 := t.t35
  t38 := t.t38
  t40 := t.t40
  t41 := t.t41

/-- leaf-fold3's added-leaf bundle from leaf-fold4's. -/
theorem addedLeaves3_of_open4 (r : OpenResearchLeaves2) (l : OpenAddedLeaves4) : OpenAddedLeaves3 where
  cmOptimalEmbedding := l.cmOptimalEmbedding
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmHauptmodul := l.qmHauptmodul
  qmClassNumberOne := l.qmClassNumberOne
  qmDenZeroCM3 := qmDenZeroCM3_of_leaves4 r.r4 l.gammaStarGen l.valenceBoundGammaStar
  senTwist := l.senTwist
  finiteImageHT := l.finiteImageHT
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  isogenyQuasiInverse := l.isogenyQuasiInverse
  divisiblePoints := l.divisiblePoints
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := l.qmAutCard
  serreRigidity3 := l.serreRigidity3
  alFixedPoints := l.alFixedPoints
  properSmoothGenConnected := properSmoothGenConnected_of_zariski4 l.zariskiConnectedness

/-- leaf-fold3's glue bundle from leaf-fold4's leaves and glue. -/
theorem glue3_of_open4 (t : OpenTextbookLeaves4) (l : OpenAddedLeaves4) (g : OpenGlue4) : OpenGlue3 where
  periodMapGlue := fun h => periodMapGlue_of_leaves4 h t.t5 t.homLatticeCorr l.cmDescends
  hauptmodulUnique := hauptmodulUnique_proved4
  chartProper := chartProper_proved4
  chartQuasiFinite := chartQuasiFinite_proved4
  heckeVertWitness := g.heckeVertWitness
  abVarSpreadsOut := abVarSpreadsOut_of_ega4 l.egaIV_8_8_2_ii l.egaIV_8_10_5_xii l.egaIV_17_7_8_ii

/-- **G0 with only the open leaves and the open glue** (leaf-fold4; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from
* `OpenResearchLeaves2`: 26 research-level fields (unchanged);
* `OpenTextbookLeaves4`: 19 textbook fields (T26 now from T5);
* `OpenAddedLeaves4`: 21 leaves;
* `OpenGlue4`: 1 glue Prop (`HeckeVertWitness`).
The table of every field is `docs/research/leaf-fold4.md` §2. -/
theorem sixContactMin_of_open4 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeaves4) (g : OpenGlue4) : ZInQ.SixContactMin :=
  sixContactMin_of_open3 r (textbookLeaves3_of_open4 t) (addedLeaves3_of_open4 r l)
    (glue3_of_open4 t l g)

end HSyn

end

#print axioms HSyn.chartProper_proved4
#print axioms HSyn.chartQuasiFinite_proved4
#print axioms HSyn.hauptmodulUnique_proved4
#print axioms HSyn.autOInnerFinite_proved4
#print axioms HSyn.leafSkolemNoether_proved4
#print axioms HSyn.t11aRiemannHom_of_corr4
#print axioms HSyn.periodMapGlue_of_leaves4
#print axioms HSyn.qmDenZeroCM3_of_leaves4
#print axioms HSyn.properSmoothGenConnected_of_zariski4
#print axioms HSyn.abVarSpreadsOut_of_ega4
#print axioms HSyn.torsionStructureK_of4
#print axioms HSyn.tateModuleFree_of_t5'
#print axioms HSyn.textbookLeaves3_of_open4
#print axioms HSyn.addedLeaves3_of_open4
#print axioms HSyn.glue3_of_open4
#print axioms HSyn.sixContactMin_of_open4
