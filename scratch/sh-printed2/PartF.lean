import ShP

/-! # sh-printed2, Part F: the research bundle with the strictly henselian forms

`OpenResearchLeaves12SH` is leaf-fold12's `OpenResearchLeaves12` (copied verbatim, 32 fields) with
`blr_1_2_4` replaced by `blr_1_2_4_SH`, `sga7_IX_3_3` replaced by `sga7_IX_3_3_SH`, and sh-route's
`neronBaseChangeSH` added (33 fields). `researchLeaves11_of_open12SH` is leaf-fold12's
`researchLeaves11_of_open12` with the two changed fields. -/

namespace HDec

namespace HSyn

structure OpenResearchLeaves12SH : Prop where
  /-- H-1 (`r1r2`), printed form: the fine moduli scheme `Y` of abelian schemes with `𝒪`-action and level 3
  (`R1fpPropsAb`) with the coarse `X₆`, the Hecke, recognition and `π₀` clauses of `R1R2fpRep`. Replaces `r1r2`. -/
  r1r2Ab : LeafAdopt.R1R2fpRepAb
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
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
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.BostLowerBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
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
  /-- shimura-split, r5count, printed form: González–Rotger 2006 Prop. 5.6 at `(D, N) = (6, 1)` on the points of
  one canonical coarse witness `X₆` of the fine moduli scheme of abelian schemes. Replaces
  `gonzalezRotgerCountX6`. -/
  gonzalezRotgerCountX6Ab : _root_.ShimuraSplit.GonzalezRotgerCountX6Ab
  /-- reduct-split, r6: SGA 7 I Exp. IX Prop. 4.7 (Raynaud's criterion) over a DVR (published form pending the
  base review). -/
  raynaudSemistable : _root_.ReductSplit.RaynaudSemistable
  /-- reduct-split, SS1/SS3: SGA 7 I Exp. IX 3.3, first assertion, over a DVR (published form pending the base
  review). -/
  semistablePersistsDVR : _root_.ReductSplit.SemistablePersistsDVR
  /-- r1univ-rigid: **Mumford's rigidity over a base, printed core** (GIT Thm 6.14 on each connected component and
  Cor. 6.4 over `S`; numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with identity `e`, and every `S`-endomorphism fixing `e` is a homomorphism. -/
  mumfordRigidityCore : _root_.LeafQM.AV.R1UnivRigid.MumfordRigidityCore
  /-- sh-printed2, printed form: Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 4 in the
  strict-henselization reading (over a Dedekind domain with fraction field of characteristic 0, a smooth
  separated model of finite type is a Néron model iff its base changes to the strict henselizations at the
  closed points are; locator UNVERIFIED). Replaces c-to-printed's `blr_1_2_4`. -/
  blr_1_2_4_SH : _root_.SHPrinted2.BLR_1_2_4_SH
  /-- c-to-printed, printed form: Faltings 1983, Lemma 5 (the change of the Faltings height under an isogeny
  through `log #s*Ω¹` of its kernel; locator UNVERIFIED). With `raynaudKernelBound` replaces `faltingsLemma5BC`. -/
  faltingsLemma5Printed : _root_.CToPrinted.FaltingsLemma5Printed
  /-- c-to-printed, printed form: Raynaud's bound on the kernel term in Faltings' Lemma 5 (locator UNVERIFIED). -/
  raynaudKernelBound : _root_.CToPrinted.RaynaudKernelBound
  /-- c-to-printed, printed form: SGA 3 VI_B 3.10 (the identity component `G⁰` of a smooth group scheme is open;
  number UNVERIFIED). With the next two and `geomConnOfRationalPoint` replaces `semistableNeronBaseChange`. -/
  sga3_VIB_3_10 : _root_.CToPrinted.SGA3_VIB_3_10
  /-- sh-printed2, printed form: SGA 7 IX 3.3 over strictly henselian traits (`N⁰ ⊗ R' ≅ N'⁰` for
  semistable reduction, characteristic 0; locator UNVERIFIED). Replaces c-to-printed's `sga7_IX_3_3`. -/
  sga7_IX_3_3_SH : _root_.SHPrinted2.SGA7_IX_3_3_SH
  /-- sh-route / sh-printed2, printed form: Bosch–Lütkebohmert–Raynaud, *Néron models*, §7.2 Thm. 1 / §1.2
  Prop. 2 (Néron models commute with strict henselization, in characteristic 0; locator UNVERIFIED). With
  `sga7_IX_3_3_SH` replaces `sga7_IX_3_3`. -/
  neronBaseChangeSH : _root_.ShRoute.NeronBaseChangeSH
  /-- c-to-printed, printed form: EGA IV 8.10.5, open immersions descend through limits (locator UNVERIFIED). -/
  egaIV_8_10_5_openImm : _root_.CToPrinted.EGAIV_8_10_5_openImm

theorem researchLeaves11_of_open12SH (r : OpenResearchLeaves12SH) (t : OpenTextbookLeaves10) :
    OpenResearchLeaves11 where
  r1r2Ab := r.r1r2Ab
  shimuraFamilyAb := r.shimuraFamilyAb
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
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
  semistableNeronBaseChange := _root_.SHPrinted2.semistableNeronBaseChange_of_printed_full0
    (_root_.SHPrinted2.blr_1_2_4_0_of_SH r.blr_1_2_4_SH) r.sga3_VIB_3_10
    (_root_.SHPrinted2.sga7_IX_3_3_0_of_SH r.sga7_IX_3_3_SH r.neronBaseChangeSH r.sga3_VIB_3_10
      t.geomConnOfRationalPoint) r.egaIV_8_10_5_openImm t.geomConnOfRationalPoint
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  faltingsLemma5BC := _root_.CToPrinted.faltingsLemma5BC_of_printed r.faltingsLemma5Printed r.raynaudKernelBound
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14
  semistableReductionDVR := r.semistableReductionDVR
  semistableUnipotent := r.semistableUnipotent
  neronSchemeModelExistsDVR := r.neronSchemeModelExistsDVR
  gonzalezRotgerCountX6Ab := r.gonzalezRotgerCountX6Ab
  raynaudSemistable := r.raynaudSemistable
  semistablePersistsDVR := r.semistablePersistsDVR
  neronLocalizesDVR := _root_.SHPrinted2.neronLocalizesDVR_of_SH r.blr_1_2_4_SH
  mumfordRigidityCore := r.mumfordRigidityCore

/-- **G0 with the strictly henselian forms** (sh-printed2): `ZInQ.SixContactMin` from
`OpenResearchLeaves12SH` (33), `OpenTextbookLeaves10` (15), `OpenAddedLeaves11` (13) and `OpenGlue7` (1). -/
theorem sixContactMin_of_open15SH (r : OpenResearchLeaves12SH) (t : OpenTextbookLeaves10)
    (l : OpenAddedLeaves11) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open14 (researchLeaves11_of_open12SH r t) t l g

end HSyn

end HDec

#print axioms HDec.HSyn.researchLeaves11_of_open12SH
#print axioms HDec.HSyn.sixContactMin_of_open15SH
