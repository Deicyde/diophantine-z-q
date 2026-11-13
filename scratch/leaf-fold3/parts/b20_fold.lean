/-! ## leaf-fold2: the results proved since leaf-fold, folded into the statement of what remains open

Task leaf-fold2, 2026-11-13. Everything above this part is `scratch/h-decomposition/Leaves.lean`
(with the ten unused `TextbookLeaves` fields deleted, see `mk_prefix.py`), g0-assemble2's 41 parts
(`GluePieces3`, `ResearchLeaves3`, `sixContactMin_of_leaves3`) and g9-abvarbc's
`ZInQKernel/Contrib/AbVarBC` (part b10, copied over this file's objects). The kernel theorems used
below are imported (`ZInQKernel.Contrib.T14.Main`, `ZInQKernel.Contrib.T28.Assemble`,
`ZInQKernel.Contrib.RLeaf.X1ConstantField`, which imports T36 and T37) and image-plane's
`scratch/image-plane/ImagePlaneFinal.lean` (module `LF2ImagePlane`, verbatim). Each closed field
is a theorem `HSyn.xxx_proved` whose type is this file's own Prop and whose proof is the imported
or copied theorem: Lean checks that the two statements agree (definitional unfolding; for the
statements over `ToP1`, a structure of which the kernel has its own copy, through the explicit
field-by-field map `toP1K`). -/

noncomputable section

namespace HSyn

open CategoryTheory AlgebraicGeometry G0Split

/-! ### Textbook leaves closed since leaf-fold -/

/-- **T14(a′) proved** (task t1415-tc / `ZInQKernel/Contrib/T14/Main.lean`). -/
theorem t14a_proved : PkgI6.BrauerHasse2C := _root_.ZInQ.Contrib.T14.brauerHasse2C

/-- **T14(b′) proved** (`ZInQKernel/Contrib/T14/Main.lean`). -/
theorem t14b_proved : PkgI6.BrauerReciprocity2C := _root_.ZInQ.Contrib.T14.brauerReciprocity2C

/-- **T28 proved** (`ZInQKernel/Contrib/T28/Assemble.lean`). T28 is not used by the proof (its
field was deleted from `TextbookLeaves`, see `mk_prefix.py`); recorded for completeness. -/
theorem t28_proved : PkgI1.IgusaClebschSeparation :=
  _root_.T28.igusaClebschSeparation_proved

/-- **T36 proved** (`ZInQKernel/Contrib/RLeaf/T36Torsion.lean`). -/
theorem t36_proved : X1Belyi.TorsionStructure := _root_.ZInQ.RLeaf.t36_torsionStructure

/-- **T37 proved** (`ZInQKernel/Contrib/RLeaf/T37GoodReduction.lean`). -/
theorem t37_proved : X1Belyi.GoodReductionUnramified :=
  _root_.ZInQ.RLeaf.T37.t37_goodReductionUnramified

/-- **T39 from T40** (`ZInQKernel/Contrib/RLeaf/X1ConstantField.lean`): a degree-one place of
`K_N` makes `ℚ` algebraically closed in `K_N`. -/
theorem t39_of_t40 (h : X1Belyi.X1RationalCusp) : X1Belyi.X1ConstantField :=
  _root_.ZInQ.RLeaf.x1ConstantField_of_x1RationalCusp h

/-! ### Curve facts closed (infra-smooth-dim, image-plane): `MobiusGlue` from T5 alone -/

/-- This file's `ToP1` as the kernel's (`ZInQKernel/HDecomp/QM/Pairs.lean`), field by field. -/
def toP1K {X : Scheme.{0}} (σ : LeafQM.AV.ToP1 X) : _root_.LeafQM.AV.ToP1 X :=
  ⟨σ.U, σ.V, σ.cover, σ.f, σ.g, σ.inv, σ.basicOpen_f, σ.basicOpen_g⟩

/-- **C1b proved** (infra-smooth-dim; image-plane's copy `LeafQM.AV.Pin.smoothStalkDimOne`). -/
theorem smoothStalkDimOne_proved : LeafQM.AV.Pin.SmoothStalkDimOne :=
  _root_.LeafQM.AV.Pin.smoothStalkDimOne

/-- **C2K proved** (image-plane, `LeafQM.AV.Pin.constOrOntoAlgClosed`). -/
theorem constOrOntoAlgClosed_proved : LeafQM.AV.Pin.ConstOrOntoAlgClosed :=
  fun K _ _ X f hP hS σ => _root_.LeafQM.AV.Pin.constOrOntoAlgClosed K X f hP hS (toP1K σ)

/-- **C3K proved** (image-plane, `LeafQM.AV.Pin.ratFactorAlgClosed`). -/
theorem ratFactorAlgClosed_proved : LeafQM.AV.Pin.RatFactorAlgClosed :=
  fun K _ _ _ X f hP hS σ ρ => _root_.LeafQM.AV.Pin.ratFactorAlgClosed K X f hP hS (toP1K σ) (toP1K ρ)

/-- **`MobiusGlue` from T5 alone** (mobius-glue, curve-facts with the three facts above). -/
theorem mobiusGlue_of_t5' (h5 : PkgI2.TorsionStructure.{0}) : LeafQM.AV.Pin.MobiusGlue :=
  LeafQM.AV.Pin.mobiusGlue_of_curves'
    (LeafQM.AV.Pin.curveFacts_of_leaves smoothStalkDimOne_proved constOrOntoAlgClosed_proved
      ratFactorAlgClosed_proved).1
    (LeafQM.AV.Pin.curveFacts_of_leaves smoothStalkDimOne_proved constOrOntoAlgClosed_proved
      ratFactorAlgClosed_proved).2
    h5

/-! ### Abelian-variety glue closed (g9-abvarbc, part b10) -/

/-- **`MulIsogeny` proved** (g9-abvarbc; replaces the leaf `mulEtale` of `GluePieces3`, which was
used only through `mulIsogeny_of_mulEtale`). -/
theorem mulIsogeny_proved : G0FibreSimple.MulIsogeny := ZInQ.Contrib.AbVarBC.mulIsogeny

/-- **`KerUnitOpen` proved** (g9-abvarbc; mul-rigidity's leaf, implied by `MulEtale`). Not needed
below (`MulIsogeny` is proved directly); recorded for completeness. -/
theorem kerUnitOpen_proved : MulRigidity.KerUnitOpen := ZInQ.Contrib.AbVarBC.kerUnitOpen

/-- **F2 of G9 proved** (g9-abvarbc: `G9Bridge.AbVarBaseChange` from Mathlib alone). -/
theorem g9AbVarBaseChange_proved : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  ZInQ.Contrib.AbVarBC.abVarBaseChange

/-- **G9 from the amended R10** (r10-amend's result, over this file's objects): the weight clause
`R10Weights` is the second half of `PkgI4.DeRhamComparisonHT`. -/
theorem g9Glue_of_deRhamComparisonHT (h : PkgI4.DeRhamComparisonHT) : G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange g9AbVarBaseChange_proved
    (PkgI4.deRhamComparisonHT_iff.mp h).2

/-! ### Kernel-field and conj-twist glue closed (their later commits; parts a75, b05) -/

/-- **`OMaximal` proved** (kernel-field, `G0ModField.KernelField.oMaximal`, pure algebra). -/
theorem oMaximal_proved : G0ModField.KernelField.OMaximal := G0ModField.KernelField.oMaximal

/-- **`EndTransport` proved** (kernel-field: from `EndTransportBC`, which follows from
`RigidityHom`, proved by mul-rigidity). -/
theorem endTransport_proved : G0ModField.KernelField.EndTransport :=
  G0ModField.KernelField.endTransport_of
    (G0ModField.KernelField.endTransportBC_of_rigidity G0FibreSimple.rigidityHom)

/-- **`ConjTwistNontrivial` from T5, T26, T35 and the leaf N2** (conj-twist's final theorem): the
glue `ArtinTorsionSurj` and `ConjUniformization` of `GluePieces3` are no longer needed. -/
theorem conjTwistNontrivial_proved (h5 : PkgI2.TorsionStructure.{0}) (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hN2 : G0Galois.HomLinearLift) :
    G0Galois.ConjTwistNontrivial :=
  G0Galois.conjTwistNontrivial_of_leaves h5 hT h35 hN2

/-! ### Height-bc glue closed (infra-stalks, part b07) -/

/-- **`CotangentSpanBC` proved** (infra-stalks, from the stalk of a fibre product). -/
theorem cotangentSpanBC_proved : ZInQ.HeightBC.CotangentSpanBC := ZInQ.HeightBC.cotangentSpanBC

/-- **`UniformizationLiftAnalytic` proved** (infra-stalks). -/
theorem uniformizationLiftAnalytic_proved : ZInQ.HeightBC.UniformizationLiftAnalytic :=
  ZInQ.HeightBC.uniformizationLiftAnalytic

/-- **`ProductUnifSplits` proved** (product-unif, part b08: elementary analysis). -/
theorem productUnifSplits_proved : ZInQ.ProductHeight.ProductUnifSplits :=
  ZInQ.ProductUnif.productUnifSplits

/-- This file's def-faltings `AbVar` as the kernel's `PkgI3.AbVar` (`ZInQKernel/HDecomp/Objects.lean`),
field by field. -/
def toAbVarK {L : Type} [Field L] (B : ZInQ.DefFaltings.AbVar L) : _root_.PkgI3.AbVar L := ⟨B.X⟩

/-- **`TangentDimAtOrigin` proved** (infra-smooth-dim, module `LF2SmoothDim`; transferred through
`toAbVarK`). -/
theorem tangentDimAtOrigin_proved : ZInQ.DefFaltings.HodgeLattice.TangentDimAtOrigin :=
  fun L _ B g hg => _root_.LF2.HodgeLattice.tangentDimAtOrigin L (toAbVarK B) g hg

/-- **`ProductMetrizationOfProductUnif` from the textbook leaf T35** (unif-dims, part b09, with
`TangentDimAtOrigin` proved). -/
theorem productMetrizationOfProductUnif_of_t35 (h35 : ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.ProductHeight.ProductMetrizationOfProductUnif :=
  ZInQ.UnifDims.productMetrizationOfProductUnif_of_tangentDim h35 tangentDimAtOrigin_proved

/-- **`UnramifiedConjugates` proved** (inner-twist, module `LF2UnramConj`, Mathlib only). -/
theorem unramifiedConjugates_proved : G0ModField.UnramifiedConjugates :=
  _root_.G0ModField.unramifiedConjugates

/-! ### The open statements -/

/-- **The research-level leaves still open** (leaf-fold2). `ResearchLeaves3` (g0-assemble2: no
`opaque` placeholder) with four fields in their published, corrected or concrete form:
* `r1b`: R1(b) concretely, in family form (fibre-qm-period's `R1bFamily`; was `GluePieces3.r1bFamily`
  and, before that, the `opaque` `r1an`);
* `r10`: R10 corrected (`PkgI4.DeRhamComparisonHT`, with the multiplicity-0 clause; g9-derham,
  r10-amend);
* `r14`: R14 corrected (`G0Galois.R14Det`, with the determinant clause; was also
  `GluePieces3.r14Det`);
* `r17`: R17 concretely (`LadicCond.CarayolR17'`, Carayol 1986 Thm (A); was
  `GluePieces3.carayolR17` and, before that, the `opaque` `r17`). -/
structure OpenResearchLeaves2 : Prop where
  r1r2 : LeafAdopt.R1R2fpRep
  /-- R1(b), concrete (family form), for the triple of the leaf bundle. -/
  r1b : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.R1bFamily (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
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
  /-- R10 corrected (with multiplicity `0` off `{0, −1}`). -/
  r10 : PkgI4.DeRhamComparisonHT
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  /-- R14 corrected (with the determinant clause). -/
  r14 : G0Galois.R14Det
  r15 : DeligneSerreConseq
  r16 : LeafModCurves.R16_EichlerShimuraJ1'
  /-- R17, concrete (Carayol 1986, Thm (A)). -/
  r17 : LadicCond.CarayolR17'
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r20 : ZInQ.DefFaltings.R20_FaltingsLemma5
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  /-- H5's finiteness half (its `NeronModelMinimal` half is proved, h5-glue). -/
  h5fin : ZInQ.DefFaltings.StableHeightFinite

/-- **The textbook leaves still open** (leaf-fold2): `TextbookLeaves` without the ten fields no
proof uses (deleted, `mk_prefix.py`), without the eight proved fields (`t14a`, `t14b` here;
`t15`, `t16a`, `t17`, `t18`, `t25`, `t31` by leaf-fold), and with `x1` (T36-T40) cut to T38 and
T40 (T36, T37 proved; T39 follows from T40). -/
structure OpenTextbookLeaves2 : Prop where
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : LeafPush.T09_WeilPairing.{0}
  t10 : T10Etale.T10_TateDuality
  t11a : ZInQ.LeafPush2.T11a_RiemannEnd
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomyYu
  t33 : LeafModCurves.JacobianExists ℚ
  t34 : LeafModCurves.DimJ1Genus
  t35 : ZInQ.LeafPush2.UniformizationExists
  /-- T38 (x1-belyi): a function field over `ℚ` with constant field `ℚ` is that of a smooth
  proper curve. -/
  t38 : X1Belyi.CurveOfFunctionFieldQ
  /-- T40 (x1-belyi): `K_N` has a degree-one place. -/
  t40 : X1Belyi.X1RationalCusp
  t41 : ZInQ.H5Neron.NeronModelExists

/-- **The leaves introduced by the wave 26-27 reductions** (g0-assemble2's `GluePieces3` fields of
kind LEAF or LEAF?, minus those now proved or moved to `OpenResearchLeaves2`). -/
structure OpenAddedLeaves2 : Prop where
  /-- fs5-nocm N1b′, LEAF (CM points via optimal embeddings). -/
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  /-- g0-thetapoint, LEAF? (theta-constant ratios at a CM period matrix are algebraic). -/
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- fibre-qm-period, LEAF? (pkg-I1's composite leaf: the theta-quotient Hauptmodul of `Γ*`). -/
  qmHauptmodul : PkgI1.QMHauptmodul
  /-- fibre-qm-period, LEAF (Eichler class number one, lattice form). -/
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  /-- fibre-qm-period, LEAF? (Lin–Yang's divisor of `ψ₄`). -/
  qmDenZeroCM3 : G0Split.FibreQM.QMDenZeroCM3
  /-- g0-mod-galois, LEAF (Burnside). -/
  burnsideAbsIrred : G0Galois.BurnsideAbsIrred
  /-- conj-twist N2, LEAF (Birkenhake–Lange Prop. 1.2.1). -/
  homLinearLift : G0Galois.HomLinearLift
  /-- g12-det, LEAF (Sen 1980). -/
  senTwist : G0Galois.SenTwist
  /-- g12-det, LEAF (Tate 1967, Ax–Sen–Tate). -/
  finiteImageHT : G0Galois.FiniteImageHT
  /-- weil-pairing, LEAF (T9 restated). -/
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  /-- weil-pairing, LEAF (Mumford §7-8). -/
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  /-- weil-pairing, LEAF (Mumford §4 Appl. 2). -/
  divisiblePoints : WeilPairing.DivisiblePoints
  /-- x6-kummer, LEAF? (the conic model of `X₆ = X₀(6,1)`, `Y² + 3X² + 3Z² = 0` with
  `π₆ = −16(X² + Z²)/(27Z²)`, on one witness of the leaf bundle; Kurihara 1979, Elkies 1998,
  UNVERIFIED locators). Replaces fs5-nocm's glue `X6KummerFibre` (`x6KummerFibre_of_conic`). -/
  x6ConicModel : X6Kummer.X6ConicModel

/-- **The glue still open** (leaf-fold2): g0-assemble2's `GluePieces3` fields of kind GLUE, minus
the nine now proved (`smoothStalkDimOne`, `ratFactorAlgClosed`, `g9AbVarBaseChange`, `oMaximal`,
`endTransport`, `cotangentSpanBC`, `uniformizationLiftAnalytic`, `productUnifSplits`,
`unramifiedConjugates`), the one replaced by a leaf (`x6KummerFibre`, by `x6ConicModel`) and the one now
following from the leaf T35 (`productMetrizationOfProductUnif`) and the two no longer used (`artinTorsionSurj`, `conjUniformization`: conj-twist's
final theorem needs neither). -/
structure OpenGlue2 : Prop where
  hodgeBCInjective : ZInQ.HeightBC.HodgeBCInjective
  omegaBaseChange : ZInQ.HeightBC.OmegaBaseChange
  periodMapGlue : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  hauptmodulUnique : G0Split.FibreQM.HauptmodulUnique
  cPtsTransport : G0Split.FibreQM.CPtsTransport
  propTSAll : G0ModField.PropTSAll
  conjIsogMaps : G0ModField.KernelField.ConjIsogMaps
  modelG3 : G0AssembleMod.ModelG3
  linkedTateLocal : G0AssembleMod.LinkedTateLocal

/-! ### From the open statements back to g0-assemble2's bundles -/

theorem researchLeaves3_of_open2 (r : OpenResearchLeaves2) : ResearchLeaves3 where
  r1r2 := r.r1r2
  r1rec := r.r1rec
  r3 := r.r3
  r4 := r.r4
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r7a := r.r7a
  r7b := r.r7b
  r8 := r.r8
  r9a := r.r9a
  r9b := r.r9b
  r10 := PkgI4.deRhamComparison_of_HT r.r10
  r11r12 := r.r11r12
  r13 := r.r13
  r14 := eigenformRepExists_of_r14Det r.r14
  r15 := r.r15
  r16 := r.r16
  r18 := r.r18
  r19 := r.r19
  r20 := r.r20
  r21 := r.r21
  r22 := r.r22
  h5fin := r.h5fin

theorem x1Leaves_of_open2 (t : OpenTextbookLeaves2) : X1Belyi.X1Leaves where
  torsion := t36_proved
  goodRed := t37_proved
  curve := t.t38
  constants := t39_of_t40 t.t40
  cusp := t.t40

theorem textbookLeaves_of_open2 (t : OpenTextbookLeaves2) : TextbookLeaves where
  t5 := t.t5
  t6 := t.t6
  t7 := t.t7
  t8 := t.t8
  t9 := t.t9
  t10 := t.t10
  t11a := t.t11a
  t11b := t.t11b
  t14a := t14a_proved
  t14b := t14b_proved
  t15 := t15_proved
  t16a := t16a_proved
  t17 := t17_proved
  t18 := t18_proved
  t23 := t.t23
  t24 := t.t24
  t25 := t25_proved
  t26 := t.t26
  t27 := t.t27
  t31 := t31_proved
  t33 := t.t33
  t34 := t.t34
  t35 := t.t35
  x1 := x1Leaves_of_open2 t
  t41 := t.t41

/-- **Leaves.lean's `GluePieces` from the open statements.** g0-assemble2's
`gluePieces_of_gluePieces3`, with every proved field replaced by its proof (`mulIsogeny_proved` for
`mulIsogeny_of_mulEtale gp.mulEtale`, the curve facts inside `mobiusGlue_of_t5'`, `oMaximal_proved`,
`endTransport_proved`, `cotangentSpanBC_proved`, `uniformizationLiftAnalytic_proved`, G9 from
`r.r10`, G10 from conj-twist's `conjTwistNontrivial_of_leaves`). -/
theorem gluePieces_of_open2 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2)
    (l : OpenAddedLeaves2) (g : OpenGlue2) : GluePieces :=
  let r3 := researchLeaves3_of_open2 r
  let t3 := textbookLeaves_of_open2 t
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
        g.hodgeBCInjective cotangentSpanBC_proved g.omegaBaseChange
        uniformizationLiftAnalytic_proved))
    productExists := G0Product.productExists
    reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3 r3 G0Split.dimFinite
    thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios
      (G0Split.FibreQM.fibreQMPeriod_main_rep r.r1r2 hMob l.qmHauptmodul
        t.t35 t.t11a l.qmClassNumberOne (r.r1b r.r1r2) (g.periodMapGlue r.r1r2)
        g.hauptmodulUnique l.qmDenZeroCM3 g.cPtsTransport)
      l.thetaRatiosAlgebraic
    modularConstituent := modularConstituent_of_field t3
      (G0ModField.fibreCoverExists_of_propTSAll' t.t5 g.propTSAll unramifiedConjugates_proved)
      (G0ModField.KernelField.kernelFieldExists_of_split'' t.t6 r.r7a r.r6 t.t5 t.t27
        hFS5 G0ModField.KernelField.oMaximal endTransport_proved g.conjIsogMaps)
      UnramTate.unramifiedSup_mf
      (G0AssembleMod.afterG7_of3 r3 t3
        ⟨l.burnsideAbsIrred, r.r14,
          g9Glue_of_deRhamComparisonHT r.r10,
          G0Galois.g10Glue_of_conjTwist
            (G0Galois.conjTwistNontrivial_of_leaves t.t5 t.t26 t.t35 l.homLinearLift),
          G0Galois.g12Weight_of_senTwist l.senTwist l.finiteImageHT,
          G0Galois.detTate_of_leaves l.t09SymmIsogenyExists l.isogenyQuasiInverse
            l.divisiblePoints t.t26,
          G0AssembleMod.resQFiniteIndex⟩
        (G0ModNewform.dirichletOfFinite_of_t17 t17_proved) r.r17
        Swan.swanIndependent_proved Swan.swanIntegral_proved
        Swan.adaptedExists_proved
        (G0AssembleMod.modelG3G6_of hFS
          (G0AssembleMod.modelNoncomm_of_mulIsogeny mulIsogeny_proved) g.modelG3)
        (G0AssembleMod.linkedTateData_of_local t.t7 g.linkedTateLocal))
    heightCopies := G0HeightCopies.heightCopiesAgree }

/-- **G0 with only the open leaves and the open glue** (leaf-fold2; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from
* `OpenResearchLeaves2`: 26 research-level fields (R1(b), R10, R14, R17 in concrete or corrected
  form; no `opaque` placeholder);
* `OpenTextbookLeaves2`: 18 textbook fields;
* `OpenAddedLeaves2`: 13 leaves (9 LEAF, 4 LEAF?) introduced by the wave 26-27 reductions and x6-kummer;
* `OpenGlue2`: 9 glue Props.
The table of every field, its kind and source is `docs/research/leaf-fold2.md`. -/
theorem sixContactMin_of_open2 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2)
    (l : OpenAddedLeaves2) (g : OpenGlue2) : ZInQ.SixContactMin :=
  sixContactMin_of_leavesR3 (researchLeaves3_of_open2 r) (textbookLeaves_of_open2 t)
    (gluePieces_of_open2 r t l g)

end HSyn

end

#print axioms HSyn.t14a_proved
#print axioms HSyn.t14b_proved
#print axioms HSyn.t28_proved
#print axioms HSyn.t36_proved
#print axioms HSyn.t37_proved
#print axioms HSyn.t39_of_t40
#print axioms HSyn.smoothStalkDimOne_proved
#print axioms HSyn.constOrOntoAlgClosed_proved
#print axioms HSyn.ratFactorAlgClosed_proved
#print axioms HSyn.mobiusGlue_of_t5'
#print axioms HSyn.mulIsogeny_proved
#print axioms HSyn.kerUnitOpen_proved
#print axioms HSyn.g9AbVarBaseChange_proved
#print axioms HSyn.g9Glue_of_deRhamComparisonHT
#print axioms HSyn.oMaximal_proved
#print axioms HSyn.endTransport_proved
#print axioms HSyn.conjTwistNontrivial_proved
#print axioms HSyn.cotangentSpanBC_proved
#print axioms HSyn.uniformizationLiftAnalytic_proved
#print axioms HSyn.productUnifSplits_proved
#print axioms HSyn.tangentDimAtOrigin_proved
#print axioms HSyn.productMetrizationOfProductUnif_of_t35
#print axioms HSyn.unramifiedConjugates_proved
#print axioms HSyn.researchLeaves3_of_open2
#print axioms HSyn.textbookLeaves_of_open2
#print axioms HSyn.gluePieces_of_open2
#print axioms HSyn.sixContactMin_of_open2
