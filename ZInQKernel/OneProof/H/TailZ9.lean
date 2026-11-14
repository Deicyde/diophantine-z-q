import ZInQKernel.OneProof.H.TailZ6
import ZInQKernel.OneProof.H.TailZ7
import ZInQKernel.OneProof.H.TailZ8

/-! # OneProof H, leaf-fold9: the bundles and `sixContactMin_of_open9`

The bundles `OpenResearchLeaves9`, `OpenTextbookLeaves9`, the maps to leaf-fold8's bundles and
`sixContactMin_of_open9`. The proofs used are in `TailZ5` (this task: `r1rec`, `r5` from `r1r2`), `TailZ6`
(modular-split: `r15`), `TailZ7` (reduct-split: `r7b`, `r8`), `TailZ8` (shimura-split: `r5count`)
and the CloudW07 modules (`t33`, `normalModelOfFunctionFieldQ`). docs/research/leaf-fold9.md lists every field. -/

namespace HDec

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits

/-! ## The bundles -/

/-- **The research leaves still open** (leaf-fold9): leaf-fold8's `OpenResearchLeaves8` without `r1rec`, `r5`
(proved from `r1r2`, `r1rec_of_rep`, `r5fp_of_rep`) and `r15` (proved from `dsThm966`, modular-split's
`deligneSerreConseq_of_ds`), and `r7b`, `r8` replaced by reduct-split's four published-form leaves
(`ReductSplit.serreTatePotentialGood_final`, `grothendieckMonodromy_final'`), and `r5count` replaced by shimura-split's
`GonzalezRotgerCountX6` (`ShimuraSplit.r5fpCount_of_points`). 30 fields. -/
structure OpenResearchLeaves9 : Prop where
  r1r2 : LeafAdopt.R1R2fpRep
  shimuraFamily : QMSplit.Moduli.ShimuraFamily
  r3 : _root_.ZInQ.LeafPush2.R03_LinYang
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r6 : _root_.PkgI2.RaynaudCriterion.{0}
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, SS1: Grothendieck's semistable reduction theorem, global form (SGA 7 IX 3.6). -/
  semistableReductionThm : _root_.ZInQ.HeightSplit.SemistableReductionThm
  /-- height-split, SS2: base change of the identity component in the semistable case (SGA 7 IX 3.3). -/
  semistableNeronBaseChange : _root_.ZInQ.HeightSplit.SemistableNeronBaseChange
  /-- height-split, SS3: semistability persists under finite extension (SGA 7 IX 3.3). -/
  semistablePersists : _root_.ZInQ.HeightSplit.SemistablePersists
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.BostLowerBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-16: Faltings 1983 Lemma 5 (semistable form) over every number field `L ⊇ K`, replaces
  `r20`. -/
  faltingsLemma5BC : _root_.ZInQ.HeightSplit.FaltingsLemma5BC
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r7b: Serre–Tate 1968 Thm 2 as printed (potential good reduction iff the image of inertia on
  `T_ℓ A` is finite; RISK: if printed for complete `K`, a consequence). -/
  serreTateThm2 : _root_.ReductSplit.SerreTateThm2
  /-- reduct-split, r8: SGA 7 IX Thm 3.6 over a DVR (semistable reduction after a finite extension, at every place
  above `O`). -/
  semistableReductionDVR : _root_.ReductSplit.SemistableReductionDVR
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest reading). -/
  semistableUnipotent : _root_.ReductSplit.SemistableUnipotent
  /-- reduct-split, r8: BLR §1.4 Thm 3 over a DVR (scheme form). -/
  neronSchemeModelExistsDVR : _root_.ReductSplit.NeronSchemeModelExistsDVR
  /-- shimura-split, r5count: González–Rotger 2006 Prop. 5.6 at `(D, N) = (6, 1)` on the points of one canonical
  coarse witness `X₆` (`#CM(R) = 2^{b(k)} h(R)`; the audit read Prop. 5.6). -/
  gonzalezRotgerCountX6 : _root_.ShimuraSplit.GonzalezRotgerCountX6

/-- **The textbook leaves still open** (leaf-fold9): leaf-fold8's `OpenTextbookLeaves8` without `t33` and
`normalModelOfFunctionFieldQ` (proved by cloud PR #11, `ZInQKernel/Contrib/CloudW07JacobiansCurves/`). 18 fields. -/
structure OpenTextbookLeaves9 : Prop where
  mulEtaleAbelianScheme : _root_.AvSplit.T4.MulEtaleAbelianScheme
  mumfordTorsionAlgClosed : _root_.AvSplit.MumfordTorsionAlgClosed
  homFreeFiniteAlgClosed : _root_.ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed
  charPolyIndepOfEllAlgClosed : _root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
  poincareComplement : _root_.ZInQ.Contrib.AVB1.PoincareComplement
  cartierSmooth : _root_.AVGlue.CartierSmooth
  geomConnOfRationalPoint : _root_.AVGlue.GeomConnOfRationalPoint
  groupSchemeEquidim : _root_.AVGlue.GroupSchemeEquidim
  t10 : _root_.T10Etale.T10_TateDuality
  uniformizationLeafAll : _root_.BPAnalytic.Uniformization.UniformizationLeafAll
  gagaMorphism : _root_.ZInQ.HomLattice.GAGAMorphism
  bdRInvariants : ∀ (p : ℕ) [Fact p.Prime], _root_.ZInQ.Contrib.HodgeSplit.BdRInvariants p
  yuThm11 : QMSplit.Yu.YuThm11
  dimJacobianEqGenus : _root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus
  genusX1Field : _root_.ZInQ.Contrib.CurvesG.GenusX1Field
  regularSmoothPerfect : _root_.CurveSplit.RegularSmoothPerfect
  igusaGL2 : _root_.ZInQ.RLeaf.IgusaGL2
  neronSchemeExtensionExists : _root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists

/-! ## From the new bundles to leaf-fold8's -/

/-- leaf-fold8's research bundle from leaf-fold9's. -/
theorem researchLeaves8_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9) : OpenResearchLeaves8 where
  r1r2 := r.r1r2
  shimuraFamily := r.shimuraFamily
  r1rec := r1rec_of_rep r.r1r2
  r3 := r.r3
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r5 := r5fp_of_rep r.r1r2
  r5count := _root_.ShimuraSplit.r5fpCount_of_points r.gonzalezRotgerCountX6
  r6 := r.r6
  r7a := r.r7a
  r7b := _root_.ReductSplit.serreTatePotentialGood_final r.serreTateThm2 t.mumfordTorsionAlgClosed
  r8 := _root_.ReductSplit.grothendieckMonodromy_final' r.semistableReductionDVR r.semistableUnipotent
    r.neronSchemeModelExistsDVR t.mumfordTorsionAlgClosed
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  dsThm965 := r.dsThm965
  dsThm966 := r.dsThm966
  r15 := _root_.ModularSplit.deligneSerreConseq_of_ds r.dsThm966
  r16 := r.r16
  r17 := r.r17
  semistableReductionThm := r.semistableReductionThm
  semistableNeronBaseChange := r.semistableNeronBaseChange
  semistablePersists := r.semistablePersists
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  faltingsLemma5BC := r.faltingsLemma5BC
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14

/-- leaf-fold8's textbook bundle from leaf-fold9's. -/
theorem textbookLeaves8_of_open9 (t : OpenTextbookLeaves9) : OpenTextbookLeaves8 where
  mulEtaleAbelianScheme := t.mulEtaleAbelianScheme
  mumfordTorsionAlgClosed := t.mumfordTorsionAlgClosed
  homFreeFiniteAlgClosed := t.homFreeFiniteAlgClosed
  charPolyIndepOfEllAlgClosed := t.charPolyIndepOfEllAlgClosed
  poincareComplement := t.poincareComplement
  cartierSmooth := t.cartierSmooth
  geomConnOfRationalPoint := t.geomConnOfRationalPoint
  groupSchemeEquidim := t.groupSchemeEquidim
  t10 := t.t10
  uniformizationLeafAll := t.uniformizationLeafAll
  gagaMorphism := t.gagaMorphism
  bdRInvariants := t.bdRInvariants
  yuThm11 := t.yuThm11
  t33 := _root_.ZInQ.Contrib.CloudW07JacobiansCurves.JacobianExists_proof
  dimJacobianEqGenus := t.dimJacobianEqGenus
  genusX1Field := t.genusX1Field
  normalModelOfFunctionFieldQ := _root_.ZInQ.Contrib.CloudW07JacobiansCurves.NormalModelOfFunctionFieldQ_proof
  regularSmoothPerfect := t.regularSmoothPerfect
  igusaGL2 := t.igusaGL2
  neronSchemeExtensionExists := t.neronSchemeExtensionExists

/-- **G0 with only the open leaves and the open glue** (leaf-fold9; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from `OpenResearchLeaves9` (30), `OpenTextbookLeaves9` (18), leaf-fold8's
`OpenAddedLeaves8` (14) and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is
`docs/research/leaf-fold9.md` §2. -/
theorem sixContactMin_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9) (l : OpenAddedLeaves8)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open8 (researchLeaves8_of_open9 r t) (textbookLeaves8_of_open9 t) l g

end HSyn

end HDec
