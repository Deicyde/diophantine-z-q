import ZInQKernel.Contrib.OneProof.Pi0Prune.Old

/-!
# pi0-prune (3/3): the stack `sixContactMin_of_open17` … `_open29` without the two fields

The added-leaf bundles `OpenAddedLeaves12` (TailZ22) … `17` (TailZ34) copied without the fields
`deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure` (suffix `P`), their maps copied without the two
assignments, and the stack theorems copied with the weak row (suffix `W`). The only changed term is
`x6Rows_of_open14W`, which calls `QMSplit.Moduli.x6Rows_of_leavesW` (no Deligne `π₀`, no `GeomConnOfAlgClosure`).
No `sorry`; standard axioms only.
-/

set_option linter.all false
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ22.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ22.lean:232-258 (structure without the two fields, docstring omitted)
structure OpenAddedLeaves12P : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  shimuraGoodReductionNoGuard : CurveSplitGR.ShimuraGoodReductionNoGuard
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop. 2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- qm-split, H-87/H-88: `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` (Shimura 1971 Prop. 9.2;
  Shimizu 1965). -/
  shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1
  /-- shimura-glue, printed form, on abelian schemes (route-a-fold): Deligne's theorem on the connected
  components of a Shimura variety for `G = B^×` at level `K₃` on one fine witness `Y₃` (Deligne, Sém. Bourbaki
  389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.1.3, 2.6.3; locators UNVERIFIED). -/
  deligneComponentsY3PrintedAb : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ23.lean` (base 43513d87) -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ23.lean:709-721 (the two leaves dropped)
/-- **The two `X₆` rows from the new bundles** (the term of `x6Rows_of_open13`). -/
theorem x6Rows_of_open14W (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12P) :
    LeafAdopt.R1R2fpRepW ∧ X6Kummer.X6ConicModel :=
  have hR := _root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw
  QMSplit.Moduli.x6Rows_of_leavesW
    { t5 := _root_.AvSplit.torsionStructure_of_mumford t.mumfordTorsionAlgClosed
      babaGranathR := (_root_.LeafQM.AV.R1UnivRigid.babaGranathRational_iff_ab_gl hR).mpr r.babaGranathRationalAb
      rayClass := (_root_.LeafQM.AV.R1UnivRigid.rayClassCM_iff_ab_gl hR).mpr r.rayClassCMAb
      gonzalezRotger := (_root_.LeafQM.AV.R1UnivRigid.gonzalezRotgerX6_iff_ab_gl hR).mpr r.gonzalezRotgerX6Ab
      elkiesEq := (_root_.LeafQM.AV.R1UnivRigid.elkiesEquationsX6_iff_ab_gl hR).mpr r.elkiesEquationsX6Ab }

-- pi0-prune: copied from TailZ23.lean:737-757
/-- leaf-fold10's added-leaf bundle from leaf-fold14's (the composite of `addedLeaves11_of_open12`,
`addedLeaves10_of_open11` and `addedLeaves9_of_open10`). -/
theorem addedLeaves9_of_open14W (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12P) :
    OpenAddedLeaves9 where
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := (x6Rows_of_open14W r t l).2
  shimuraTaniyamaQbar := l.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  shimuraGoodReductionNoGuard := l.shimuraGoodReductionNoGuard
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
  igusaCMValue24 := _root_.CM24.igusaCMValue24_field
  deligneComponentsY3Printed :=
    (_root_.LeafQM.AV.R1UnivRigid.deligneComponentsY3Printed_iff_ab_gl
      (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw)).mpr
      l.deligneComponentsY3PrintedAb

-- pi0-prune: copied from TailZ23.lean:759-767
/-- **SS1 and SS3** (`semistableReductionThm`, `semistablePersists`) from the restricted printed leaf
`semistablePersistsSHcp`, the pair, 3.6 (K1), BLR 1.4/3 and the glue of `TailZ15` (`semistableLocalGlobal` from
`blr_1_2_4` through c-to-printed's `neronLocalizesDVR_of_printed`; `semistableAlmostAll_of10`). -/
theorem ss1_ss3_of14W (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12P) :
    _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists :=
  _root_.ReductB.ss1_ss3_of_cp r.semistablePersistsSHcp r.strictHenselizationPair (semistableReductionDVR_of14 r t)
    r.neronSchemeModelExistsDVR
    (_root_.ReductGlue.semistableLocalGlobal_leaf (_root_.CToPrinted.neronLocalizesDVR_of_printed r.blr_1_2_4))
    (semistableAlmostAll_of10 (addedLeaves9_of_open14W r t l))

-- pi0-prune: copied from TailZ23.lean:769-807
/-- leaf-fold9's research bundle from leaf-fold14's (the composite of `researchLeaves12_of_open13`,
`researchLeaves11_of_open12`, `researchLeaves10_of_open11` and `researchLeaves9_of_open10`, with the three reduct
fields replaced by reduct-b's theorems and SS1, SS3 by `ss1_ss3_of14W`). -/
theorem researchLeaves9_of_open14W (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12P) :
    OpenResearchLeaves9W where
  r1r2 := (x6Rows_of_open14W r t l).1
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
  semistableReductionThm := (ss1_ss3_of14W r t l).1
  semistableNeronBaseChange := _root_.CToPrinted.semistableNeronBaseChange_of_printed_full r.blr_1_2_4
    r.sga3_VIB_3_10 r.sga7_IX_3_3 r.egaIV_8_10_5_openImm t.geomConnOfRationalPoint
  semistablePersists := (ss1_ss3_of14W r t l).2
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

-- pi0-prune: copied from TailZ23.lean:809-815
/-- **G0 with only the open leaves and the open glue** (leaf-fold14, reduct fold; no `sorry`, standard axioms).
`ZInQ.SixContactMin` from `OpenResearchLeaves14` (35), `OpenTextbookLeaves10` (15), `OpenAddedLeaves12P` (14) and
`OpenGlue7` (1). -/
theorem sixContactMin_of_open17W (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12P)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open11W (researchLeaves9_of_open14W r t l) t (addedLeaves9_of_open14W r t l) g
    (_root_.CToPrinted.faltingsLemma5BCLower_of_printed r.faltingsLemma5Printed) hYu

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ24.lean` (base 43513d87) -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj
namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ24.lean:769-810 (structure without the two fields, docstring omitted)
structure OpenAddedLeaves13P : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  shimuraGoodReductionNoGuard : CurveSplitGR.ShimuraGoodReductionNoGuard
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop. 2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- qm-split, H-87/H-88: `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` (Shimura 1971 Prop. 9.2;
  Shimizu 1965). -/
  shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1
  /-- shimura-glue, printed form, on abelian schemes (route-a-fold): Deligne's theorem on the connected
  components of a Shimura variety for `G = B^×` at level `K₃` on one fine witness `Y₃` (Deligne, Sém. Bourbaki
  389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.1.3, 2.6.3; locators UNVERIFIED). -/
  deligneComponentsY3PrintedAb : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb
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

-- pi0-prune: copied from TailZ24.lean:814-830 (two assignments dropped)
/-- x6-fold's added-leaf bundle from leaf-fold14's: `t09SymmIsogenyExists` from t09-pic's four printed leaves. -/
theorem addedLeaves12_of_open13W (l : OpenAddedLeaves13P) : OpenAddedLeaves12P where
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := _root_.T09Pic.t09SymmIsogenyExists_of_four l.picRepresentableAbVar l.picZeroAbVar
    l.phiAmpleIsogeny l.weilPairingMumford
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  shimuraTaniyamaQbar := l.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  shimuraGoodReductionNoGuard := l.shimuraGoodReductionNoGuard
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
  deligneComponentsY3PrintedAb := l.deligneComponentsY3PrintedAb

-- pi0-prune: copied from TailZ24.lean:832-837
/-- **G0 with only the open leaves and the open glue** (leaf-fold14; no `sorry`, standard axioms).
`ZInQ.SixContactMin` from `OpenResearchLeaves14` (35), `OpenTextbookLeaves10` (15), `OpenAddedLeaves13P` (17) and
`OpenGlue7` (1). -/
theorem sixContactMin_of_open18W (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves13P)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open17W r t (addedLeaves12_of_open13W l) g hYu

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ25.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ25.lean:136-138
/-- **G0 with only the open leaves and the open glue** (gt-ega; generated). -/
theorem sixContactMin_of_open19W (r : OpenResearchLeaves15) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves13P) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open18W (openResearchLeaves14_of_OpenResearchLeaves15 r) t l g hYu

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ26.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ26.lean:132-170 (structure without the two fields, docstring omitted)
structure OpenAddedLeaves14P : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  shimuraGoodReductionNoGuard : CurveSplitGR.ShimuraGoodReductionNoGuard
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop. 2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- shimura-glue, printed form, on abelian schemes (route-a-fold): Deligne's theorem on the connected
  components of a Shimura variety for `G = B^×` at level `K₃` on one fine witness `Y₃` (Deligne, Sém. Bourbaki
  389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.1.3, 2.6.3; locators UNVERIFIED). -/
  deligneComponentsY3PrintedAb : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb
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

-- pi0-prune: copied from TailZ26.lean:172-190 (two assignments dropped)
/-- `OpenAddedLeaves13P` from `OpenAddedLeaves14P`: `shimizuCovolumeO1` by the contributions. -/
theorem openAddedLeaves13_of_OpenAddedLeaves14W (n : OpenAddedLeaves14P) : OpenAddedLeaves13P where
  thetaRatiosAlgebraic := n.thetaRatiosAlgebraic
  qmCentralizerCMC := n.qmCentralizerCMC
  tateTwistInvariants := n.tateTwistInvariants
  axSenTate := n.axSenTate
  milneIsogenyQuasiInverse := n.milneIsogenyQuasiInverse
  shimuraTaniyamaQbar := n.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := n.egaIV_8_10_5_xii
  shimuraGoodReductionNoGuard := n.shimuraGoodReductionNoGuard
  valenceFormulaCocompactEq := n.valenceFormulaCocompactEq
  shimizuCovolumeO1 := _root_.HDec.GammaStarArea.shimizuCovolumeO1_proof
  deligneComponentsY3PrintedAb := n.deligneComponentsY3PrintedAb
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := n.picZeroAbVar
  phiAmpleIsogeny := n.phiAmpleIsogeny
  weilPairingMumford := n.weilPairingMumford

-- pi0-prune: copied from TailZ26.lean:192-194
/-- **G0 with only the open leaves and the open glue** (leaf-fold16; generated). -/
theorem sixContactMin_of_open20W (r : OpenResearchLeaves16) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves14P) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open19W (openResearchLeaves15_of_OpenResearchLeaves16 r) t (openAddedLeaves13_of_OpenAddedLeaves14W l) g hYu

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ27.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ27.lean:124-126
/-- **G0 with only the open leaves and the open glue** (gt-grcount-fold; generated). -/
theorem sixContactMin_of_open21W (r : OpenResearchLeaves17) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves14P) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open20W (openResearchLeaves16_of_OpenResearchLeaves17 r) t l g hYu

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ28.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ28.lean:123-125
/-- **G0 with only the open leaves and the open glue** (leaf-fold18; generated). -/
theorem sixContactMin_of_open22W (r : OpenResearchLeaves18) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves14P) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open21W (openResearchLeaves17_of_OpenResearchLeaves18 r) t l g hYu

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ29.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ29.lean:120-122
/-- **G0 with only the open leaves and the open glue** (leaf-fold18; generated). -/
theorem sixContactMin_of_open23W (r : OpenResearchLeaves19) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves14P) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open22W (openResearchLeaves18_of_OpenResearchLeaves19 r) t l g hYu

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ30.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ30.lean:14-51 (structure without the two fields, docstring omitted)
structure OpenAddedLeaves15P : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  shimuraGoodReductionNoGuard : CurveSplitGR.ShimuraGoodReductionNoGuard
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop. 2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- shimura-glue, printed form, on abelian schemes (route-a-fold): Deligne's theorem on the connected
  components of a Shimura variety for `G = B^×` at level `K₃` on one fine witness `Y₃` (Deligne, Sém. Bourbaki
  389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.1.3, 2.6.3; locators UNVERIFIED). -/
  deligneComponentsY3PrintedAb : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb
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

-- pi0-prune: copied from TailZ30.lean:53-70 (two assignments dropped)
/-- `OpenAddedLeaves14P` from `OpenAddedLeaves15P`: `qmCentralizerCMC` by the contributions. -/
theorem openAddedLeaves14_of_OpenAddedLeaves15W (n : OpenAddedLeaves15P) (t : OpenTextbookLeaves10) : OpenAddedLeaves14P where
  thetaRatiosAlgebraic := n.thetaRatiosAlgebraic
  qmCentralizerCMC := _root_.HDec.QMLattice.qmCentralizerCMC_of t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed
  tateTwistInvariants := n.tateTwistInvariants
  axSenTate := n.axSenTate
  milneIsogenyQuasiInverse := n.milneIsogenyQuasiInverse
  shimuraTaniyamaQbar := n.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := n.egaIV_8_10_5_xii
  shimuraGoodReductionNoGuard := n.shimuraGoodReductionNoGuard
  valenceFormulaCocompactEq := n.valenceFormulaCocompactEq
  deligneComponentsY3PrintedAb := n.deligneComponentsY3PrintedAb
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := n.picZeroAbVar
  phiAmpleIsogeny := n.phiAmpleIsogeny
  weilPairingMumford := n.weilPairingMumford

-- pi0-prune: copied from TailZ30.lean:72-75
/-- **G0 with only the open leaves and the open glue** (leaf-fold18; generated). -/
theorem sixContactMin_of_open24W (r : OpenResearchLeaves19) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves15P) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open23W r t (openAddedLeaves14_of_OpenAddedLeaves15W l t) g
    (QMLattice.yuB6Alg_of' t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed)

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ31.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ31.lean:14-48 (structure without the two fields, docstring omitted)
structure OpenAddedLeaves16P : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  shimuraGoodReductionNoGuard : CurveSplitGR.ShimuraGoodReductionNoGuard
  /-- shimura-glue, printed form, on abelian schemes (route-a-fold): Deligne's theorem on the connected
  components of a Shimura variety for `G = B^×` at level `K₃` on one fine witness `Y₃` (Deligne, Sém. Bourbaki
  389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.1.3, 2.6.3; locators UNVERIFIED). -/
  deligneComponentsY3PrintedAb : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb
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

-- pi0-prune: copied from TailZ31.lean:50-66 (two assignments dropped)
/-- `OpenAddedLeaves15P` from `OpenAddedLeaves16P`: `valenceFormulaCocompactEq` by the contributions. -/
theorem openAddedLeaves15_of_OpenAddedLeaves16W (n : OpenAddedLeaves16P) : OpenAddedLeaves15P where
  thetaRatiosAlgebraic := n.thetaRatiosAlgebraic
  tateTwistInvariants := n.tateTwistInvariants
  axSenTate := n.axSenTate
  milneIsogenyQuasiInverse := n.milneIsogenyQuasiInverse
  shimuraTaniyamaQbar := n.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := n.egaIV_8_10_5_xii
  shimuraGoodReductionNoGuard := n.shimuraGoodReductionNoGuard
  valenceFormulaCocompactEq := _root_.ValenceCocompact.valenceFormulaCocompactEq_proof
  deligneComponentsY3PrintedAb := n.deligneComponentsY3PrintedAb
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := n.picZeroAbVar
  phiAmpleIsogeny := n.phiAmpleIsogeny
  weilPairingMumford := n.weilPairingMumford

-- pi0-prune: copied from TailZ31.lean:68-70
/-- **G0 with only the open leaves and the open glue** (leaf-fold18; generated). -/
theorem sixContactMin_of_open25W (r : OpenResearchLeaves19) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves16P) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open24W r t (openAddedLeaves15_of_OpenAddedLeaves16W l) g

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ32.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ32.lean:44-46
/-- **G0 with only the open leaves and the open glue** (leaf-fold19; generated). -/
theorem sixContactMin_of_open26W (r : OpenResearchLeaves19) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves16P) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open25W r (openTextbookLeaves10_of_OpenTextbookLeaves11 t) l g

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ33.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ33.lean:121-123
/-- **G0 with only the open leaves and the open glue** (leaf-fold20; generated). -/
theorem sixContactMin_of_open27W (r : OpenResearchLeaves20) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves16P) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open26W (openResearchLeaves19_of_OpenResearchLeaves20 r t) t l g

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ34.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ34.lean:117-152 (structure without the two fields, docstring omitted)
structure OpenAddedLeaves17P : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- shimura-glue, printed form, on abelian schemes (route-a-fold): Deligne's theorem on the connected
  components of a Shimura variety for `G = B^×` at level `K₃` on one fine witness `Y₃` (Deligne, Sém. Bourbaki
  389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.1.3, 2.6.3; locators UNVERIFIED). -/
  deligneComponentsY3PrintedAb : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb
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

-- pi0-prune: copied from TailZ34.lean:154-169 (two assignments dropped)
/-- `OpenAddedLeaves16P` from `OpenAddedLeaves17P`: `shimuraGoodReductionNoGuard` by the contributions. -/
theorem openAddedLeaves16_of_OpenAddedLeaves17W (n : OpenAddedLeaves17P) : OpenAddedLeaves16P where
  thetaRatiosAlgebraic := n.thetaRatiosAlgebraic
  tateTwistInvariants := n.tateTwistInvariants
  axSenTate := n.axSenTate
  milneIsogenyQuasiInverse := n.milneIsogenyQuasiInverse
  shimuraTaniyamaQbar := n.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := n.egaIV_8_10_5_xii
  shimuraGoodReductionNoGuard := _root_.SGRSplit.shimuraGoodReductionNoGuard_of_printed n.shimuraIntegralModelRep
  deligneComponentsY3PrintedAb := n.deligneComponentsY3PrintedAb
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := n.picZeroAbVar
  phiAmpleIsogeny := n.phiAmpleIsogeny
  weilPairingMumford := n.weilPairingMumford

-- pi0-prune: copied from TailZ34.lean:171-173
/-- **G0 with only the open leaves and the open glue** (leaf-fold22; generated). -/
theorem sixContactMin_of_open28W (r : OpenResearchLeaves21) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17P) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open27W (openResearchLeaves20_of_OpenResearchLeaves21 r t) t (openAddedLeaves16_of_OpenAddedLeaves17W l) g

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ35.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ35.lean:115-117
/-- **G0 with only the open leaves and the open glue** (r16-split; generated). -/
theorem sixContactMin_of_open29W (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17P) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open28W (openResearchLeaves21_of_OpenResearchLeaves22 r t) t l g

end HSyn
end HDec
