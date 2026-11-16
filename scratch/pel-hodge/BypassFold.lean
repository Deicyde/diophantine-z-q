import ZInQKernel.OneProof.H.TailZ35
import ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used
import ZInQKernel.Contrib.OneProof.CompositeOut
import ZInQKernel.Contrib.OneProof.HolFamilyPrinted
import ZInQKernel.Contrib.OneProof.PELHodge
import ZInQKernel.OneProof.TYZSplit
import ZInQKernel.OneProof.TopChain
import ZInQKernel.Contrib.TYZChain.Main
import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.OneProof.FHNonvanishing

/-! # pel-hodge: holfam's bypass fold dry run with `pelHolFamilyHodge` (PELHodge) in place of `pelHolFamily`
(scratch; not a module of the tree). Copied from scratch/holfam/BypassFold.lean; the only changes: the field
`pelHolFamily` is replaced by `pelHolFamilyHodge : PELHodge.PELHolFamilyHodge`, and its two uses
`HolFamilyPrinted.shimuraHolModAll_of_pel n.pelHolFamily` by
`PELHodge.shimuraHolModAll_of_hodge t.uniformizationLeafAll n.pelHolFamilyHodge`.

(holfam:) composite-out's bypass fold dry run with `pelHolFamily` (HolFamilyPrinted) in place of
`shimuraHolModAll` (scratch; not a module of the tree). Copied from scratch/composite-out/BypassFold.lean; the only
changes: the field `shimuraHolModAll` is replaced by `pelHolFamily : HolFamilyPrinted.PELHolFamily`, and its two uses
by `HolFamilyPrinted.shimuraHolModAll_of_pel n.pelHolFamily`.

(composite-out:)

The research bundle loses `shimuraMainThmIDeligneY3AbU` and gains `mainTheoremCM` (qmrec-printed) and
`shimuraHolModAll` (shimura-split2): `OpenResearchLeaves23`. It maps to leaf-fold22's `OpenResearchLeaves20`
(`openResearchLeaves20_of_23`), and dcy3-used's `y3Connected` is filled by `CompositeOut.y3Connected_of_modAll`.
The rest is dcy3-used's dry run, unchanged:

(dcy3-used:)

`deligneComponentsY3PrintedAb` is removed from the added bundle (`OpenAddedLeaves18`). Its only use, `y3Connected`
of leaf-fold8's `OpenAddedLeaves8` (`TailZ13.addedLeaves8_of_open9`), is filled by
`DCY3Used.y3Connected_of_leaves r.mumfordGroupLaw r.shimuraMainThmIDeligneY3AbU`. The new bundle cannot be mapped
to `OpenAddedLeaves17` nor to any older generation down to leaf-fold10's `OpenAddedLeaves9` (all carry the field),
so the new top theorem maps straight to `sixContactMin_of_open10` (the generation where `y3Connected` is a field):
the research and textbook maps of `TailZ25`-`TailZ35` are composed unchanged; `TailZ23`'s `x6Rows_of_open14`,
`ss1_ss3_of14` (with `TailZ15.semistableAlmostAll_of10` inlined) and `researchLeaves9_of_open14`, and the added
maps of `TailZ24`-`TailZ34`, `TailZ23.addedLeaves9_of_open14`, `TailZ13.addedLeaves8_of_open9` are copied with the
same terms. -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)

namespace HDec

namespace HSyn

/-- **The added leaves still open** (dcy3-used): `OpenAddedLeaves17` without `deligneComponentsY3PrintedAb`, whose
only use is filled by `DCY3Used.y3Connected_of_leaves`. 14 fields. -/
structure OpenAddedLeaves18 : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- x6-glue (shimura-glue), printed form (on abelian schemes): Deligne's theorem on the connected components of a
  Shimura variety (Sém. Bourbaki 389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.6.3; locators UNVERIFIED) for
  `G = B^×` at level `𝒪̂^×` on one canonical coarse witness `X₆` (the double coset is computed in Lean). -/
  deligneComponentsX6PrintedAb : _root_.ShimuraGlue.DeligneComponentsX6PrintedAb
  /-- x6-glue (shimura-split), textbook, weakened: for a proper `X → Spec k`, `char k = 0`, connectedness of
  `X ×_k k̄` gives geometric connectedness (EGA IV 4.5; Stacks 0389; locators UNVERIFIED). -/
  geomConnOfAlgClosure : QMSplit.Moduli.GeomConnOfAlgClosure
  /-- t09-pic, L1, printed form: the relative Picard fppf sheaf of an abelian variety over a field is representable
  (Murre 1964, Oort 1962; FGA Exp. 232 Thm 3.1; Kleiman, *The Picard scheme*, Thm 9.4.8 with 9.2.5; locators
  UNVERIFIED). With the next three replaces `t09SymmIsogenyExists`. -/
  picRepresentableAbVar : _root_.T09Pic.PicRepresentableAbVar
  /-- t09-pic, L2, printed form: for every representation of `Pic_{A/K}`, its identity component with the induced
  group law is an abelian variety (`IsPicZero`; Mumford §13, Kleiman 9.5.1 and 9.5.3, SGA 3 VI_A 2.4; locators
  UNVERIFIED). -/
  picZeroAbVar : _root_.T09Pic.PicZeroAbVar
  /-- t09-pic, L3, printed form: for ample `L`, the lift `λ_L : A → Pic⁰` of `φ_L` is an isogeny (Mumford §6
  Application 1 and §8 Thm 1; locators UNVERIFIED). -/
  phiAmpleIsogeny : _root_.T09Pic.PhiAmpleIsogeny
  /-- t09-pic, L4, printed form (single leaf): there is a pairing `A[n] × Pic⁰[n] → μ_n`, `n` invertible in `K`, with
  the values of Mumford's `ē_n` (`weilScalar`), perfect, Galois-equivariant, compatible in `n`, adjoint for the
  genuine dual `f^∨`, and trivial on `(x, λ_L x)` for ample `L` (Mumford §20 and §23; Milne 1986 §16; locators
  UNVERIFIED). -/
  weilPairingMumford : _root_.T09Pic.WeilPairingMumford
  /-- Representability over Z_(p), p > 324, of the moduli problem of QM abelian surfaces (disc 6) with full level 3, by a proper smooth curve (printed form on QMAbScheme): Kottwitz, J. AMS 5 (1992) 5; Buzzard, Duke 87 (1997) 1-4; Morita, Hokkaido 10 (1981); locators UNVERIFIED -/
  shimuraIntegralModelRep : _root_.SGRSplit.ShimuraIntegralModelRep

/-- `OpenResearchLeaves22` without `shimuraMainThmIDeligneY3AbU`, with the leaves `mainTheoremCM`, `pelHolFamily` (holfam; composite-out had `shimuraHolModAll`)
(composite-out). -/
structure OpenResearchLeaves23 : Prop where
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
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
  /-- reduct-split, r8: BLR §1.4 Thm 3 over a DVR (scheme form). -/
  neronSchemeModelExistsDVR : _root_.ReductSplit.NeronSchemeModelExistsDVR
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  mumfordGroupLaw : _root_.ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw
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
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
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
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- qmrec-printed: the main theorem of complex multiplication, adelic form with torsion (printed form;
  Shimura 1998 Thm 18.6, Milne ISV Thm 11.2, locators UNVERIFIED). -/
  mainTheoremCM : _root_.QMRecPrinted.MainTheoremCM
  /-- holfam: the PEL moduli scheme M_{K3} over ℚ with its universal QM abelian scheme and its holomorphic complex
  uniformization `τ ↦ [τ, 1]` (Deligne 1971 §4 / Ex. 5.8; published, pending reading of the analytic clause). -/
  pelHolFamilyHodge : _root_.PELHodge.PELHolFamilyHodge

/-- leaf-fold22's research bundle 20 from the new one: `TailZ35`'s and `TailZ34`'s maps composed, with
`shimuraFamilyAb` (shimura-split2) and `rayClassCMAb` (qmrec-printed) from the new leaves. -/
theorem openResearchLeaves20_of_23 (n : OpenResearchLeaves23) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves18) :
    OpenResearchLeaves20 where
  shimuraFamilyAb := _root_.ShimuraSplit2.shimuraFamilyAb_of_leaves2 l.deligneComponentsX6PrintedAb (_root_.PELHodge.shimuraHolModAll_of_hodge t.uniformizationLeafAll n.pelHolFamilyHodge)
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm965 := n.dsThm965
  dsThm966 := n.dsThm966
  r16 := _root_.R16Split.r16_of_printed n.r16CoreY t.mumfordTorsionAlgClosed t.charPolyIndepOfEllAlgClosed
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  neronSchemeModelExistsDVR := n.neronSchemeModelExistsDVR
  mumfordGroupLaw := n.mumfordGroupLaw
  faltingsLemma5Printed := n.faltingsLemma5Printed
  sga3_VIB_3_10 := n.sga3_VIB_3_10
  babaGranathRationalAb := n.babaGranathRationalAb
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  rayClassCMAb := _root_.QMRecPrinted.rayClassCMAb_of_mainCM l.deligneComponentsX6PrintedAb n.mainTheoremCM
    t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed
  raynaudSemistableSH := n.raynaudSemistableSH
  semistablePersistsSHcp := n.semistablePersistsSHcp
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  elkiesX6StarPrinted := n.elkiesX6StarPrinted
  sga7_IX_3_3_SH := n.sga7_IX_3_3_SH
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom

theorem x6Rows_of18 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves18) :
    LeafAdopt.R1R2fpRep ∧ X6Kummer.X6ConicModel :=
  have hR := _root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw
  QMSplit.Moduli.x6Rows_of_leaves
    { deligneX6P := (_root_.LeafQM.AV.R1UnivRigid.deligneComponentsX6Printed_iff_ab_gl hR).mpr
        l.deligneComponentsX6PrintedAb
      geomConn := l.geomConnOfAlgClosure
      t5 := _root_.AvSplit.torsionStructure_of_mumford t.mumfordTorsionAlgClosed
      babaGranathR := (_root_.LeafQM.AV.R1UnivRigid.babaGranathRational_iff_ab_gl hR).mpr r.babaGranathRationalAb
      rayClass := (_root_.LeafQM.AV.R1UnivRigid.rayClassCM_iff_ab_gl hR).mpr r.rayClassCMAb
      gonzalezRotger := (_root_.LeafQM.AV.R1UnivRigid.gonzalezRotgerX6_iff_ab_gl hR).mpr r.gonzalezRotgerX6Ab
      elkiesEq := (_root_.LeafQM.AV.R1UnivRigid.elkiesEquationsX6_iff_ab_gl hR).mpr r.elkiesEquationsX6Ab }



/-- SS1 and SS3 (the term of `TailZ23.ss1_ss3_of14`, with `semistableAlmostAll_of10` inlined: it reads only
`egaIV_8_10_5_xii`). -/
theorem ss1_ss3_of18 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves18) :
    _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists :=
  _root_.ReductB.ss1_ss3_of_cp r.semistablePersistsSHcp r.strictHenselizationPair (semistableReductionDVR_of14 r t)
    r.neronSchemeModelExistsDVR
    (_root_.ReductGlue.semistableLocalGlobal_leaf (_root_.CToPrinted.neronLocalizesDVR_of_printed r.blr_1_2_4))
    (_root_.ReductGlue.semistableAlmostAll_of
      (abVarSpreadsOut_of_ega4 _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof l.egaIV_8_10_5_xii
        _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii_proof)
      (properSmoothGenConnected_of_zariski4 _root_.ZariskiConn.ZariskiConnectedness_proof.{0}))

theorem researchLeaves9_of18 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves18) :
    OpenResearchLeaves9 where
  r1r2 := (x6Rows_of18 r t l).1
  shimuraFamily := (_root_.LeafQM.AV.R1UnivRigid.shimuraFamily_iff_ab_gl
      (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw)).mpr
    r.shimuraFamilyAb
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r6 := _root_.ReductGlue.raynaudCriterion_leaves (raynaudSemistable_of14 r t) r.semistableUnipotent
    r.neronSchemeModelExistsDVR t.mumfordTorsionAlgClosed t.mulEtaleAbelianScheme
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
  semistableReductionThm := (ss1_ss3_of18 r t l).1
  semistableNeronBaseChange := _root_.CToPrinted.semistableNeronBaseChange_of_printed_full r.blr_1_2_4
    r.sga3_VIB_3_10 r.sga7_IX_3_3 r.egaIV_8_10_5_openImm t.geomConnOfRationalPoint
  semistablePersists := (ss1_ss3_of18 r t l).2
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14
  semistableReductionDVR := semistableReductionDVR_of14 r t
  semistableUnipotent := r.semistableUnipotent
  neronSchemeModelExistsDVR := r.neronSchemeModelExistsDVR
  gonzalezRotgerCountX6 :=
    (_root_.LeafQM.AV.R1UnivRigid.gonzalezRotgerCountX6_iff_ab_gl
      (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw)).mpr
      r.gonzalezRotgerCountX6Ab


/-- leaf-fold8's added bundle from the new one (the composite of the added maps of `TailZ34`, `TailZ31`, `TailZ30`,
`TailZ26`, `TailZ24`, `TailZ23.addedLeaves9_of_open14` and `TailZ13.addedLeaves8_of_open9`, same terms), with
`y3Connected` from `CompositeOut.y3Connected_of_modAll` (composite-out; dcy3-used used the composite). -/
theorem addedLeaves8_of18 (r22 : OpenResearchLeaves23) (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10)
    (l : OpenAddedLeaves18) : OpenAddedLeaves8 where
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmCentralizerCMC := _root_.HDec.QMLattice.qmCentralizerCMC_of t.uniformizationLeafAll t.gagaMorphism
    t.mumfordTorsionAlgClosed
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := _root_.T09Pic.t09SymmIsogenyExists_of_four l.picRepresentableAbVar l.picZeroAbVar
    l.phiAmpleIsogeny l.weilPairingMumford
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := (x6Rows_of18 r t l).2
  y3Connected := _root_.CompositeOut.y3Connected_of_modAll r22.mumfordGroupLaw l.deligneComponentsX6PrintedAb
    (_root_.PELHodge.shimuraHolModAll_of_hodge t.uniformizationLeafAll r22.pelHolFamilyHodge) r22.mainTheoremCM t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed
  shimuraTaniyamaQbar := l.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  shimuraGoodReductionNoGuard := _root_.SGRSplit.shimuraGoodReductionNoGuard_of_printed l.shimuraIntegralModelRep
  valenceFormulaCocompactEq := _root_.ValenceCocompact.valenceFormulaCocompactEq_proof
  shimizuCovolumeO1 := _root_.HDec.GammaStarArea.shimizuCovolumeO1_proof
  igusaCMValue24 := _root_.CM24.igusaCMValue24_field

/-- **G0 with only the open leaves and the open glue** (composite-out on dcy3-used bypass; no `sorry`, standard axioms). -/
theorem sixContactMin_of_open31 (r : OpenResearchLeaves23) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves18)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  let t10 := openTextbookLeaves10_of_OpenTextbookLeaves11 t
  let r14 := openResearchLeaves14_of_OpenResearchLeaves15 (openResearchLeaves15_of_OpenResearchLeaves16
    (openResearchLeaves16_of_OpenResearchLeaves17 (openResearchLeaves17_of_OpenResearchLeaves18
      (openResearchLeaves18_of_OpenResearchLeaves19 (openResearchLeaves19_of_OpenResearchLeaves20
        (openResearchLeaves20_of_23 r t l) t)))))
  sixContactMin_of_open10 (researchLeaves9_of18 r14 t10 l) t10 (addedLeaves8_of18 r r14 t10 l) g
    (_root_.CToPrinted.faltingsLemma5BCLower_of_printed r14.faltingsLemma5Printed)
    (QMLattice.yuB6Alg_of' t10.uniformizationLeafAll t10.gagaMorphism t10.mumfordTorsionAlgClosed)

end HSyn

end HDec

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- `frozenTarget` on the new bundle (copy of `Main.lean`'s, `l : OpenAddedLeaves18`, `sixContactMin_of_open31`). -/
theorem frozenTarget_pelHodge
    (r : HDec.HSyn.OpenResearchLeaves23) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves18)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open31 r t l g)
    (tyzThm35ReadingA_of_leaves h11 h29 (_root_.T5Glue.shimuraReciprocityModFn_of_printed hCM hX) (ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 h33))
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3

end ZInQ.Contrib.TYZChain

#print axioms HDec.HSyn.sixContactMin_of_open31
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_pelHodge
