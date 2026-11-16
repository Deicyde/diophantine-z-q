import ZInQKernel.OneProof.H.TailZ14

/-! # OneProof H, leaf-fold10: the bundle `OpenResearchLeaves10` and `sixContactMin_of_open12`

The research fields `r6` (`PkgI2.RaynaudCriterion`), `semistableReductionThm` and `semistablePersists` (SS1, SS3;
height-split), all three consequences of one theorem, are proved from reduct-glue's work (`TailZ14`) and replaced
by three leaves: `ReductSplit.RaynaudSemistable` (SGA 7 IX 4.7 over a DVR), `ReductSplit.SemistablePersistsDVR`
(SGA 7 IX 3.3 over a DVR) and `ReductGlue.NeronLocalizesDVR` (BLR §1.2 Prop. 4). SS1 also uses the field
`semistableReductionDVR` (`ReductSplit.SemistableReductionDVR`, SGA 7 IX Thm 3.6 over a DVR), already in
leaf-fold9's bundle. The glue that reduct-split left for these rows is proved:
`FixedTorsionRationalImperfect` from the textbook field `mulEtaleAbelianScheme`,
`SemistableLocalGlobal` from `NeronLocalizesDVR`, and `SemistableAlmostAll` from the kernel's `AbVarSpreadsOut`
(from the EGA IV leaves: the added field `egaIV_8_10_5_xii` and cloud worker W01's two proofs) and Zariski's
connectedness theorem (cloud worker W02's proof). docs/research/leaf-fold10.md lists every field. -/

namespace HDec

namespace HSyn

/-! ## The bundle -/

/-- **The research leaves still open** (leaf-fold10): leaf-fold9's `OpenResearchLeaves9` without `r6`,
`semistableReductionThm` and `semistablePersists`, with `raynaudSemistable`, `semistablePersistsDVR` and
`neronLocalizesDVR` added (reduct-glue). 30 fields. -/
structure OpenResearchLeaves10 : Prop where
  r1r2 : LeafAdopt.R1R2fpRepW
  shimuraFamily : QMSplit.Moduli.ShimuraFamily
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
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
  /-- height-split, SS2: base change of the identity component in the semistable case (SGA 7 IX 3.3). -/
  semistableNeronBaseChange : _root_.ZInQ.HeightSplit.SemistableNeronBaseChange
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
  /-- reduct-split, r6: SGA 7 I Exp. IX Prop. 4.7 (Raynaud's criterion) over a DVR: if the points of order
  `m ≥ 3` (`m` invertible in `O`) are rational over `K`, then `A` has semistable reduction at `O` (published form
  pending the base review: the print may be over a strictly henselian base; reduct-glue §4). Replaces `r6`. -/
  raynaudSemistable : _root_.ReductSplit.RaynaudSemistable
  /-- reduct-split, SS1/SS3: SGA 7 I Exp. IX 3.3, first assertion, over a DVR (semistability persists along a
  finite extension; published form pending the base review). Replaces, with the next field,
  `semistableReductionThm` and `semistablePersists`. -/
  semistablePersistsDVR : _root_.ReductSplit.SemistablePersistsDVR
  /-- reduct-glue: BLR, Néron models, §1.2 Prop. 4, the "only if" direction, over every DVR of a number field
  (a Néron model over `𝓞_L` base changes to a Néron model over every discrete valuation ring of `L`; every such
  ring is a localization at a maximal ideal, proved by reduct-glue). -/
  neronLocalizesDVR : _root_.ReductGlue.NeronLocalizesDVR

/-! ## From the new bundle to leaf-fold9's -/

/-- reduct-split's glue `SemistableLocalGlobal` from the field `neronLocalizesDVR` (reduct-glue). -/
theorem semistableLocalGlobal_of10 (r : OpenResearchLeaves10) : _root_.ReductSplit.SemistableLocalGlobal :=
  _root_.ReductGlue.semistableLocalGlobal_leaf r.neronLocalizesDVR

/-- reduct-split's glue `SemistableAlmostAll` (reduct-glue's `semistableAlmostAll_of`) from the kernel's
`AbVarSpreadsOut` (`abVarSpreadsOut_of_ega4`: the added field `egaIV_8_10_5_xii` and cloud worker W01's proofs
of EGA IV 8.8.2 (ii), 17.7.8 (ii)) and `ProperSmoothGenConnected` (cloud worker W02's Zariski connectedness). -/
theorem semistableAlmostAll_of10 (l : OpenAddedLeaves9) : _root_.ReductSplit.SemistableAlmostAll :=
  _root_.ReductGlue.semistableAlmostAll_of
    (abVarSpreadsOut_of_ega4 _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof l.egaIV_8_10_5_xii
      _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii_proof)
    (properSmoothGenConnected_of_zariski4 _root_.ZariskiConn.ZariskiConnectedness_proof.{0})

/-- leaf-fold9's research bundle from leaf-fold10's. -/
theorem researchLeaves9_of_open10 (r : OpenResearchLeaves10) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves9) :
    OpenResearchLeaves9 where
  r1r2 := r.r1r2
  shimuraFamily := r.shimuraFamily
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r6 := PkgI2.raynaudCriterionNF_of_general (_root_.ReductGlue.raynaudCriterion_leaves r.raynaudSemistable
    r.semistableUnipotent r.neronSchemeModelExistsDVR t.mumfordTorsionAlgClosed t.mulEtaleAbelianScheme)
  r7a := r.r7a
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  dsThm965 := r.dsThm965
  dsThm966 := r.dsThm966
  r16 := r.r16
  r17 := r.r17
  semistableReductionThm := _root_.ReductSplit.semistableReductionThm_final r.semistableReductionDVR
    r.semistablePersistsDVR r.neronSchemeModelExistsDVR (semistableLocalGlobal_of10 r)
    (semistableAlmostAll_of10 l)
  semistableNeronBaseChange := r.semistableNeronBaseChange
  semistablePersists := _root_.ReductSplit.semistablePersists_final r.semistablePersistsDVR
    r.neronSchemeModelExistsDVR (semistableLocalGlobal_of10 r)
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14
  gonzalezRotgerCountX6 := r.gonzalezRotgerCountX6

/-- **G0 with only the open leaves and the open glue** (leaf-fold10; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from `OpenResearchLeaves10` (30), `OpenTextbookLeaves10` (17), `OpenAddedLeaves9` (14)
and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is
`docs/research/leaf-fold10.md` §2. -/
theorem sixContactMin_of_open12 (r : OpenResearchLeaves10) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves9)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) (hY3 : TSHecke.Y3Connected) : ZInQ.SixContactMin :=
  sixContactMin_of_open11 (researchLeaves9_of_open10 r t l) t l g
    (_root_.ZInQ.HeightSplit.faltingsLemma5BCLower_of_BC r.faltingsLemma5BC) hYu hY3

end HSyn

end HDec
