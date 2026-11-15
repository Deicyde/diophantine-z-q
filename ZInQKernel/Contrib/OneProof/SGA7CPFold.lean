import ZInQKernel.OneProof.H.TailZ34
import ZInQKernel.Contrib.OneProof.SGA7CP

/-! # sga7-cp generation module: `sixContactMin_of_open29` with the two SGA 7 IX leaves restricted

Hand fold (task sga7-cp, docs/research/sga7-cp.md), written so that it can be moved verbatim to
`ZInQKernel/OneProof/H/TailZ35.lean`, with `Main.lean` switched to `sixContactMin_of_open29` and the binder
`r : HDec.HSyn.OpenResearchLeaves22`.

`OpenResearchLeaves22` is `OpenResearchLeaves21` with two fields replaced by their restrictions to characteristic `0`
and perfect residue field (each a specialization of the field it replaces, so the bundle is weaker):
* `raynaudSemistableSH : ReductGlue.RaynaudSemistableSH` by `raynaudSemistableSHcp : ReductB.RaynaudSemistableSHcp`;
* `sga7_IX_3_5_ForwardGeom : UnipotentForward.SGA7_IX_3_5_ForwardGeom` by
  `sga7_IX_3_5_ForwardGeomCP : SGA7CP.SGA7_IX_3_5_ForwardGeomCP`.

The weaker bundle cannot be mapped to `OpenResearchLeaves21` (a Prop bundle must be built in full), so the new top
theorem bypasses generations 14-21: it maps the bundles straight to the inputs of `sixContactMin_of_open11` (TailZ13),
the newest stack theorem whose hypotheses are the consumers of the two fields (r6 and SS1/SS3 are fields of
`OpenResearchLeaves9`). The research terms are the composites of `openResearchLeaves14_of_…15` … `20_of_…21`
(TailZ25-TailZ34; computed by scratch/sga7-cp/compose.py) substituted into `researchLeaves9_of_open14`,
`x6Rows_of_open14`, `mumfordRigidity_of14`, `addedLeaves9_of_open14` (TailZ23), and the other bundles go through the
existing conversions, as in `sixContactMin_of_open17` … `_open28`. r6 and SS1/SS3 come from
`SGA7CP.raynaudCriterionNF_of_cpLeaves` and `SGA7CP.ss1_ss3_of_cpLeaves` in place of `raynaudCriterionNF_of14` and
`ss1_ss3_of14NF` (TailZ26).
-/

namespace HDec

namespace HSyn

/-- `OpenResearchLeaves21` with `raynaudSemistableSH` and `sga7_IX_3_5_ForwardGeom` replaced by their restrictions to
characteristic `0` and perfect residue field (sga7-cp). 28 fields. -/
structure OpenResearchLeaves22 : Prop where
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
  /-- r1univ-rigid: **Mumford's rigidity over a base, printed core** (GIT Thm 6.14 on each connected component and
  Cor. 6.4 over `S`; numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with identity `e`, and every `S`-endomorphism fixing `e` is a homomorphism. -/
  mumfordRigidityCore : _root_.LeafQM.AV.R1UnivRigid.MumfordRigidityCore
  /-- c-to-printed, printed form: Faltings 1983, Lemma 5 (the change of the Faltings height under an isogeny
  through `log #s*Ω¹` of its kernel; locator UNVERIFIED). With `raynaudKernelBound` replaces `faltingsLemma5BC`. -/
  faltingsLemma5Printed : _root_.CToPrinted.FaltingsLemma5Printed
  /-- c-to-printed, printed form: SGA 3 VI_B 3.10 (the identity component `G⁰` of a smooth group scheme is open;
  number UNVERIFIED). With the next two and `geomConnOfRationalPoint` replaces `semistableNeronBaseChange`. -/
  sga3_VIB_3_10 : _root_.CToPrinted.SGA3_VIB_3_10
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- sga7-cp, printed form, restricted: Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED), over a
  strictly henselian DVR `O` of a field of characteristic `0` with perfect (hence algebraically closed) residue field:
  if `m ≥ 3` is invertible in `O` and the points of order `m` are rational over `K`, then `A` has semistable Néron
  models at `O`. A specialization of `raynaudSemistableSH` (`SGA7CP.raynaudSemistableSHcp_of_SH`) and of every
  reading of the print. Replaces `raynaudSemistableSH`, whose only uses (r6 at number fields, SS1/SS3) are at strict
  henselizations of DVRs of number fields. -/
  raynaudSemistableSHcp : _root_.ReductB.RaynaudSemistableSHcp
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Prop. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- gt-grcount, printed form: Gonzalez-Rotger 2006 Prop. 5.6 at (D,N) = (6,1) on X0(6,1), for every witness of the moduli description (no existence claim; the model comes from gonzalezRotgerX6Ab). Replaces gonzalezRotgerCountX6Ab. -/
  gonzalezRotgerProp56X6 : _root_.GRCountX6.GonzalezRotgerProp56X6
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models commute with strict henselization), for unramified strictly henselian extensions with separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- gt-elkies: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, printed form on the canonical witness: t is a coordinate on X6/W (fibres on Qbar-points = orbits of W = {1,w2,w3,w6}, defined by their moduli action), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesEquationsX6Ab (the moduli step orbit_iff_twist is proved). -/
  elkiesX6StarPrinted : _root_.HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted
  /-- gt-sga7, printed form: SGA 7 I, Exp. IX, Prop. 3.3, second assertion (N0 x_S S' = N'0 for semistable reduction) over strictly henselian traits (number UNVERIFIED). With neronBaseChangeStrictHenselization, sga3_VIB_3_10 and geomConnOfRationalPoint replaces sga7_IX_3_3 (SGA7PersistsNF.sga7_IX_3_3_of_SH). -/
  sga7_IX_3_3_SH : _root_.SGA7PersistsNF.SGA7_IX_3_3_SH
  /-- sga7-cp, printed form, restricted: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on
  T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (number UNVERIFIED), over a strictly henselian DVR of
  a field of characteristic `0` with perfect (hence algebraically closed) residue field. A specialization of
  `sga7_IX_3_5_ForwardGeom` (`SGA7CP.forwardGeomCP_of_forwardGeom`) and a consequence of the reading-robust form
  with no glue (`SGA7CP.forwardGeomCP_of_forward`: for perfect residue fields semistability over k(s) and on the
  geometric fibre agree). Replaces `sga7_IX_3_5_ForwardGeom`, whose only use (r6 at number fields) is at strict
  henselizations of DVRs of number fields. -/
  sga7_IX_3_5_ForwardGeomCP : _root_.SGA7CP.SGA7_IX_3_5_ForwardGeomCP
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU

/-- **The new bundle is weaker than the old** (sanity; off the chain): `OpenResearchLeaves22` from
`OpenResearchLeaves21`, the two restricted fields by specialization. -/
theorem openResearchLeaves22_of_OpenResearchLeaves21 (r : OpenResearchLeaves21) : OpenResearchLeaves22 where
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
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14
  mumfordRigidityCore := r.mumfordRigidityCore
  faltingsLemma5Printed := r.faltingsLemma5Printed
  sga3_VIB_3_10 := r.sga3_VIB_3_10
  babaGranathRationalAb := r.babaGranathRationalAb
  gonzalezRotgerX6Ab := r.gonzalezRotgerX6Ab
  raynaudSemistableSHcp := _root_.SGA7CP.raynaudSemistableSHcp_of_SH r.raynaudSemistableSH
  semistablePersistsSHcp := r.semistablePersistsSHcp
  gonzalezRotgerProp56X6 := r.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := r.neronBaseChangeStrictHenselization
  elkiesX6StarPrinted := r.elkiesX6StarPrinted
  sga7_IX_3_3_SH := r.sga7_IX_3_3_SH
  sga7_IX_3_5_ForwardGeomCP := _root_.SGA7CP.forwardGeomCP_of_forwardGeom r.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := r.shimuraMainThmIDeligneY3AbU

/-! ## Generations 14-21 bypassed: the research terms over the new bundle -/

/-- Mumford's rigidity from the field `mumfordRigidityCore` (as `mumfordRigidity_of14`). -/
theorem mumfordRigidity_of22 (r : OpenResearchLeaves22) : _root_.LeafQM.AV.R1UnivRigid.MumfordRigidity :=
  _root_.LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core r.mumfordRigidityCore

/-- **The two `X₆` rows from the new bundles** (the term of `x6Rows_of_open14`, with `elkiesEquationsX6Ab` and
`rayClassCMAb` from their TailZ29 and TailZ34 proofs). -/
theorem x6Rows_of_open22 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves12) :
    LeafAdopt.R1R2fpRep ∧ X6Kummer.X6ConicModel :=
  have hR := _root_.LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core r.mumfordRigidityCore
  QMSplit.Moduli.x6Rows_of_leaves
    { deligneX6P := (_root_.LeafQM.AV.R1UnivRigid.deligneComponentsX6Printed_iff_ab hR).mpr
        l.deligneComponentsX6PrintedAb
      geomConn := l.geomConnOfAlgClosure
      t5 := _root_.AvSplit.torsionStructure_of_mumford (openTextbookLeaves10_of_OpenTextbookLeaves11 t).mumfordTorsionAlgClosed
      babaGranathR := (_root_.LeafQM.AV.R1UnivRigid.babaGranathRational_iff_ab hR).mpr r.babaGranathRationalAb
      rayClass := (_root_.LeafQM.AV.R1UnivRigid.rayClassCM_iff_ab hR).mpr
        (_root_.RayClassCFT.rayClassCMAb_of_leaves r.shimuraMainThmIDeligneY3AbU t.uniformizationLeafAll t.gagaMorphism)
      gonzalezRotger := (_root_.LeafQM.AV.R1UnivRigid.gonzalezRotgerX6_iff_ab hR).mpr r.gonzalezRotgerX6Ab
      elkiesEq := (_root_.LeafQM.AV.R1UnivRigid.elkiesEquationsX6_iff_ab hR).mpr
        (_root_.HDec.QMSplit.Moduli.ElkiesX6Star.elkiesEquationsX6Ab_of_printed r.elkiesX6StarPrinted) }

/-- leaf-fold10's added-leaf bundle from the new bundles (the term of `addedLeaves9_of_open14`). -/
theorem addedLeaves9_of_open22 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves12) :
    OpenAddedLeaves9 where
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := (x6Rows_of_open22 r t l).2
  shimuraTaniyamaQbar := l.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  shimuraGoodReductionNoGuard := l.shimuraGoodReductionNoGuard
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
  igusaCMValue24 := _root_.CM24.igusaCMValue24_field
  deligneComponentsY3Printed :=
    (_root_.LeafQM.AV.R1UnivRigid.deligneComponentsY3Printed_iff_ab (mumfordRigidity_of22 r)).mpr
      l.deligneComponentsY3PrintedAb

/-- **r6 at number fields from the restricted leaves** (sga7-cp; replaces `raynaudCriterionNF_of14`). -/
theorem raynaudCriterionNF_of22 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) :
    PkgI2.RaynaudCriterionNF.{0} :=
  _root_.SGA7CP.raynaudCriterionNF_of_cpLeaves r.raynaudSemistableSHcp r.sga7_IX_3_5_ForwardGeomCP
    r.neronBaseChangeStrictHenselization t.neronSchemeExtensionExists t.mumfordTorsionAlgClosed
    _root_.ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof

/-- **SS1 and SS3 from the restricted Raynaud leaf** (sga7-cp; replaces `ss1_ss3_of14NF`). -/
theorem ss1_ss3_of22 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves12) :
    _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists :=
  _root_.SGA7CP.ss1_ss3_of_cpLeaves r.raynaudSemistableSHcp r.semistablePersistsSHcp
    r.neronBaseChangeStrictHenselization t.neronSchemeExtensionExists t.mumfordTorsionAlgClosed
    _root_.ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof
    (_root_.ReductGlue.semistableLocalGlobal_leaf (_root_.CToPrinted.neronLocalizesDVR_of_printed _root_.GapBLR.blr_1_2_4))
    (semistableAlmostAll_of10 (addedLeaves9_of_open22 r t l))

/-- leaf-fold9's research bundle from the new bundle (the term of `researchLeaves9_of_open14` with the composites of
the conversions TailZ25-TailZ34 substituted; r6 and SS1/SS3 as arguments). -/
theorem researchLeaves9_of_open22 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves12)
    (h6 : PkgI2.RaynaudCriterionNF.{0})
    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists) :
    OpenResearchLeaves9 where
  r1r2 := (x6Rows_of_open22 r t l).1
  shimuraFamily := (_root_.LeafQM.AV.R1UnivRigid.shimuraFamily_iff_ab (mumfordRigidity_of22 r)).mpr
    (_root_.RayClassCFT.shimuraFamilyAb_of_U r.shimuraMainThmIDeligneY3AbU)
  igusaPsi4 := _root_.GapTheta.igusaPsi4_proof
  igusaChi10 := _root_.GapTheta.igusaChi10_proof
  r6 := h6
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
  semistableReductionThm := hSS.1
  semistableNeronBaseChange := _root_.CToPrinted.semistableNeronBaseChange_of_printed_full _root_.GapBLR.blr_1_2_4
    r.sga3_VIB_3_10
    (_root_.SGA7PersistsNF.sga7_IX_3_3_of_SH r.sga7_IX_3_3_SH r.neronBaseChangeStrictHenselization r.sga3_VIB_3_10
      t.geomConnOfRationalPoint)
    _root_.ZInQ.Contrib.EGAOpenImm.egaIV_8_10_5_openImm_proof
    (openTextbookLeaves10_of_OpenTextbookLeaves11 t).geomConnOfRationalPoint
  semistablePersists := hSS.2
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14
  gonzalezRotgerCountX6 :=
    (_root_.LeafQM.AV.R1UnivRigid.gonzalezRotgerCountX6_iff_ab (mumfordRigidity_of22 r)).mpr
      (_root_.GRCountX6.gonzalezRotgerCountX6Ab_of_printed r.gonzalezRotgerProp56X6 r.gonzalezRotgerX6Ab)

/-- leaf-fold14's added-leaf bundle `OpenAddedLeaves12` from leaf-fold22's (the conversions of `_open28` …
`_open18`). -/
theorem addedLeaves12_of_open17 (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17) : OpenAddedLeaves12 :=
  addedLeaves12_of_open13 (openAddedLeaves13_of_OpenAddedLeaves14
    (openAddedLeaves14_of_OpenAddedLeaves15 (openAddedLeaves15_of_OpenAddedLeaves16
      (openAddedLeaves16_of_OpenAddedLeaves17 l)) (openTextbookLeaves10_of_OpenTextbookLeaves11 t)))

/-- **G0 with only the open leaves and the open glue** (sga7-cp hand fold; no `sorry`, standard axioms).
`ZInQ.SixContactMin` from `OpenResearchLeaves22` (28), `OpenTextbookLeaves11` (12), `OpenAddedLeaves17` (14) and
`OpenGlue7` (1): `sixContactMin_of_open28` with the two SGA 7 IX leaves restricted. -/
theorem sixContactMin_of_open29 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open11
    (researchLeaves9_of_open22 r t (addedLeaves12_of_open17 t l) (raynaudCriterionNF_of22 r t)
      (ss1_ss3_of22 r t (addedLeaves12_of_open17 t l)))
    (openTextbookLeaves10_of_OpenTextbookLeaves11 t) (addedLeaves9_of_open22 r t (addedLeaves12_of_open17 t l)) g
    (_root_.CToPrinted.faltingsLemma5BCLower_of_printed r.faltingsLemma5Printed)
    (QMLattice.yuB6Alg_of' (openTextbookLeaves10_of_OpenTextbookLeaves11 t).uniformizationLeafAll
      (openTextbookLeaves10_of_OpenTextbookLeaves11 t).gagaMorphism
      (openTextbookLeaves10_of_OpenTextbookLeaves11 t).mumfordTorsionAlgClosed)

end HSyn

end HDec
