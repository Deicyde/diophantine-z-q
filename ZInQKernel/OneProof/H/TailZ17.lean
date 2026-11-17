import ZInQKernel.OneProof.H.TailZ16

/-! # OneProof H, route-a-fold: the moduli leaves in their printed (abelian-scheme) form, `sixContactMin_of_open13`

Route A for `R1univProps` (r1univ-rigid, docs/research/r1univ-rigid.md; docs/research/route-a-fold.md). The four
fields of `frozenTarget` stated on the kernel's `LeafQM.AV.R1fpProps` (whose families `QMFamily S` carry no group
law) are restated on `LeafQM.AV.R1UnivRigid.R1fpPropsAb` (abelian schemes with `𝒪`-action and level 3, the objects
of the published fine-moduli problem), and one leaf is added, Mumford's rigidity in its printed core
`MumfordRigidityCore` (`TailZ16`). Each old field is filled from its printed form by
`(L_iff_ab (mumfordRigidity_of_core h)).mpr`:

* `r1r2 : LeafAdopt.R1R2fpRep` → `r1r2Ab : LeafAdopt.R1R2fpRepAb`;
* `shimuraFamily : QMSplit.Moduli.ShimuraFamily` → `shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb`;
* `gonzalezRotgerCountX6 : ShimuraSplit.GonzalezRotgerCountX6` → `gonzalezRotgerCountX6Ab : …Ab`;
* `deligneComponentsY3Printed : ShimuraGlue.DeligneComponentsY3Printed` → `deligneComponentsY3PrintedAb : …Ab`;
* new: `mumfordRigidityCore : LeafQM.AV.R1UnivRigid.MumfordRigidityCore`.

Each `LAb` is the text of `L` with `R1fpProps` replaced by `R1fpPropsAb`, in `L`'s namespace with `L`'s `open`s
(r1univ-rigid's `parts/printed.lean`, verbatim); `L_iff_ab` closes by rewriting `R1fpProps = R1fpPropsAb`, which
checks that the two texts elaborate to the same term up to that one constant. -/

/-! ## The printed forms (r1univ-rigid, `parts/printed.lean`) -/

namespace ShimuraSplit

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `ShimuraSplit.GonzalezRotgerCountX6`** (row H-145): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def GonzalezRotgerCountX6Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
      Module.finrank ℚ k = 2 →
      ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
        (∃ P : QMPair Qbar, Nonempty (com P.q ≃+* R)) →
          Nat.card {x : fieldPt Qbar ⟶ X //
              ∃ P : QMPair Qbar, Ψ x = Quotient.mk _ P ∧ Nonempty (com P.q ≃+* R)} =
            2 ^ inertCount6 k * Nat.card (CommRing.Pic R)

end ShimuraSplit

namespace ShimuraGlue

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum
attribute [local instance 2000] instAlgebraAdicCompletion

/-- **Abelian-scheme form of `ShimuraGlue.DeligneComponentsY3Printed`** (row shimura-glue): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def DeligneComponentsY3PrintedAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ DelignePi0 Y K3

end ShimuraGlue

namespace HDec.LeafAdopt

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.LeafAdopt.R1R2fpRep`** (row H-1 r1r2): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def R1R2fpRepAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6PropsIff X Ψ π₆ ∧
      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ ∧ R1pi0Props X

end HDec.LeafAdopt

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.ShimuraFamily`** (row shimuraFamily H-139): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def ShimuraFamilyAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧
    ∀ π : ToP1 Y.left, HSyn.G0Split.FibreQM.R1bFamily Y Φ π

end HDec.QMSplit.Moduli

/-! ## Each leaf from its printed form, under rigidity (r1univ-rigid, `parts/thms.lean`) -/

namespace LeafQM.AV.R1UnivRigid

/-- Row H-145: `GonzalezRotgerCountX6` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem gonzalezRotgerCountX6_iff_ab (hR : MumfordRigidity) :
    ShimuraSplit.GonzalezRotgerCountX6 ↔ ShimuraSplit.GonzalezRotgerCountX6Ab := by
  unfold ShimuraSplit.GonzalezRotgerCountX6 ShimuraSplit.GonzalezRotgerCountX6Ab
  rw [r1fpProps_eq_ab' hR]

/-- Row shimura-glue: `DeligneComponentsY3Printed` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem deligneComponentsY3Printed_iff_ab (hR : MumfordRigidity) :
    ShimuraGlue.DeligneComponentsY3Printed ↔ ShimuraGlue.DeligneComponentsY3PrintedAb := by
  unfold ShimuraGlue.DeligneComponentsY3Printed ShimuraGlue.DeligneComponentsY3PrintedAb
  rw [r1fpProps_eq_ab' hR]

/-- Row H-1 r1r2: `R1R2fpRep` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem r1R2fpRep_iff_ab (hR : MumfordRigidity) : HDec.LeafAdopt.R1R2fpRep ↔ HDec.LeafAdopt.R1R2fpRepAb := by
  unfold HDec.LeafAdopt.R1R2fpRep HDec.LeafAdopt.R1R2fpRepAb
  rw [r1fpProps_eq_ab' hR]

/-- Row shimuraFamily H-139: `ShimuraFamily` ↔ its abelian-scheme form, under `MumfordRigidity`. -/
theorem shimuraFamily_iff_ab (hR : MumfordRigidity) :
    HDec.QMSplit.Moduli.ShimuraFamily ↔ HDec.QMSplit.Moduli.ShimuraFamilyAb := by
  unfold HDec.QMSplit.Moduli.ShimuraFamily HDec.QMSplit.Moduli.ShimuraFamilyAb
  rw [r1fpProps_eq_ab' hR]

end LeafQM.AV.R1UnivRigid

namespace HDec

namespace HSyn

/-! ## The bundles -/

/-- **The research leaves still open** (route-a-fold): leaf-fold10's `OpenResearchLeaves10` with the three moduli
leaves `r1r2`, `shimuraFamily`, `gonzalezRotgerCountX6` in their printed form on abelian schemes
(`R1fpPropsAb`), and Mumford's rigidity `mumfordRigidityCore` added. 29 fields. -/
structure OpenResearchLeaves11 : Prop where
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
  /-- reduct-glue: BLR, Néron models, §1.2 Prop. 4, the "only if" direction, over every DVR of a number field. -/
  neronLocalizesDVR : _root_.ReductGlue.NeronLocalizesDVR
  /-- r1univ-rigid: **Mumford's rigidity over a base, printed core** (GIT Thm 6.14 on each connected component and
  Cor. 6.4 over `S`; numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with identity `e`, and every `S`-endomorphism fixing `e` is a homomorphism. -/
  mumfordRigidityCore : _root_.LeafQM.AV.R1UnivRigid.MumfordRigidityCore

/-- **The added leaves still open** (route-a-fold): leaf-fold10's `OpenAddedLeaves9` with
`deligneComponentsY3Printed` in its printed form on abelian schemes. 14 fields. -/
structure OpenAddedLeaves10 : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  x6ConicModel : X6Kummer.X6ConicModel
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop. 2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- qm-split, H-87/H-88: `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` (Shimura 1971 Prop. 9.2;
  Shimizu 1965). -/
  shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1
  /-- qm-glue, H-88: Lin–Yang's Igusa vector at the Baba–Granath CM value `j = −16/27` (discriminant `−24`). -/
  igusaCMValue24 : LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24

/-! ## From the new bundles to leaf-fold10's -/

/-- Mumford's rigidity (`MumfordRigidity`, with clause (b)) from the field `mumfordRigidityCore`
(r1univ-rigid's `mumfordRigidity_of_core`). -/
theorem mumfordRigidity_of11 (r : OpenResearchLeaves11) : _root_.LeafQM.AV.R1UnivRigid.MumfordRigidity :=
  _root_.LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core r.mumfordRigidityCore

/-- leaf-fold10's research bundle from route-a-fold's: the three moduli leaves from their printed forms. -/
theorem researchLeaves10_of_open11 (r : OpenResearchLeaves11) : OpenResearchLeaves10 where
  r1r2 := LeafAdopt.R1R2fpRepW_of_rep
    ((_root_.LeafQM.AV.R1UnivRigid.r1R2fpRep_iff_ab (mumfordRigidity_of11 r)).mpr r.r1r2Ab)
  shimuraFamily := (_root_.LeafQM.AV.R1UnivRigid.shimuraFamily_iff_ab (mumfordRigidity_of11 r)).mpr
    r.shimuraFamilyAb
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
  semistableNeronBaseChange := r.semistableNeronBaseChange
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  faltingsLemma5BC := r.faltingsLemma5BC
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14
  semistableReductionDVR := r.semistableReductionDVR
  semistableUnipotent := r.semistableUnipotent
  neronSchemeModelExistsDVR := r.neronSchemeModelExistsDVR
  gonzalezRotgerCountX6 :=
    (_root_.LeafQM.AV.R1UnivRigid.gonzalezRotgerCountX6_iff_ab (mumfordRigidity_of11 r)).mpr
      r.gonzalezRotgerCountX6Ab
  raynaudSemistable := r.raynaudSemistable
  semistablePersistsDVR := r.semistablePersistsDVR
  neronLocalizesDVR := r.neronLocalizesDVR

/-- leaf-fold10's added-leaf bundle from route-a-fold's: Deligne's printed theorem on `Y₃` from its
abelian-scheme form and the research field `mumfordRigidityCore`. -/
theorem addedLeaves9_of_open10 (r : OpenResearchLeaves11) (l : OpenAddedLeaves10) : OpenAddedLeaves9 where
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
  igusaCMValue24 := l.igusaCMValue24

/-- **G0 with only the open leaves and the open glue** (route-a-fold; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from `OpenResearchLeaves11` (29), `OpenTextbookLeaves10` (16), `OpenAddedLeaves10` (14)
and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The moduli leaves are stated on abelian schemes, as
printed; the table of every changed field is `docs/research/route-a-fold.md` §2. -/
theorem sixContactMin_of_open13 (r : OpenResearchLeaves11) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves10)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) (hY3 : TSHecke.Y3Connected)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) : ZInQ.SixContactMin :=
  sixContactMin_of_open12 (researchLeaves10_of_open11 r) t (addedLeaves9_of_open10 r l) g hYu hY3 hθ

end HSyn

end HDec
