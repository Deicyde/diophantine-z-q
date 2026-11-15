import ZInQKernel.OneProof.H.TailZ35
import ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used
import ZInQKernel.OneProof.TYZSplit
import ZInQKernel.OneProof.TopChain
import ZInQKernel.Contrib.TYZChain.Main
import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.OneProof.FHNonvanishing

/-! # dcy3-used: bypass fold dry run (scratch; not a module of the tree)

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
`y3Connected` from the research fields `mumfordGroupLaw` and `shimuraMainThmIDeligneY3AbU` (dcy3-used). -/
theorem addedLeaves8_of18 (r22 : OpenResearchLeaves22) (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10)
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
  y3Connected := _root_.DCY3Used.y3Connected_of_leaves r22.mumfordGroupLaw r22.shimuraMainThmIDeligneY3AbU
  shimuraTaniyamaQbar := l.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  shimuraGoodReductionNoGuard := _root_.SGRSplit.shimuraGoodReductionNoGuard_of_printed l.shimuraIntegralModelRep
  valenceFormulaCocompactEq := _root_.ValenceCocompact.valenceFormulaCocompactEq_proof
  shimizuCovolumeO1 := _root_.HDec.GammaStarArea.shimizuCovolumeO1_proof
  igusaCMValue24 := _root_.CM24.igusaCMValue24_field

/-- **G0 with only the open leaves and the open glue** (dcy3-used bypass; no `sorry`, standard axioms). -/
theorem sixContactMin_of_open30 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves18)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  let t10 := openTextbookLeaves10_of_OpenTextbookLeaves11 t
  let r14 := openResearchLeaves14_of_OpenResearchLeaves15 (openResearchLeaves15_of_OpenResearchLeaves16
    (openResearchLeaves16_of_OpenResearchLeaves17 (openResearchLeaves17_of_OpenResearchLeaves18
      (openResearchLeaves18_of_OpenResearchLeaves19 (openResearchLeaves19_of_OpenResearchLeaves20
        (openResearchLeaves20_of_OpenResearchLeaves21 (openResearchLeaves21_of_OpenResearchLeaves22 r t) t) t)))))
  sixContactMin_of_open10 (researchLeaves9_of18 r14 t10 l) t10 (addedLeaves8_of18 r r14 t10 l) g
    (_root_.CToPrinted.faltingsLemma5BCLower_of_printed r14.faltingsLemma5Printed)
    (QMLattice.yuB6Alg_of' t10.uniformizationLeafAll t10.gagaMorphism t10.mumfordTorsionAlgClosed)

end HSyn

end HDec

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- `frozenTarget` on the new bundle (copy of `Main.lean`'s, `l : OpenAddedLeaves18`, `sixContactMin_of_open30`). -/
theorem frozenTarget_dcy3
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves18)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM) (hX : _root_.T5Glue.X0ModuliGalois)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open30 r t l g)
    (tyzThm35ReadingA_of_leaves h11 h29 (_root_.T5Glue.shimuraReciprocityModFn_of_printed hCM hX) (ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 h33))
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3

end ZInQ.Contrib.TYZChain

#print axioms HDec.HSyn.sixContactMin_of_open30
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_dcy3
