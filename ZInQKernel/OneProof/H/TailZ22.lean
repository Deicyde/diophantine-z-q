import ZInQKernel.OneProof.H.TailZ21

/-! # OneProof H, x6-fold (3/3): the bundles `OpenResearchLeaves13`, `OpenAddedLeaves12` and `sixContactMin_of_open16`

x6-glue (docs/research/x6-glue.md; `TailZ20`, `TailZ21`) proves the two fields
* `r1r2Ab : LeafAdopt.R1R2fpRepAb` (research; through route-a-fold's `r1R2fpRep_iff_ab`) and
* `x6ConicModel : X6Kummer.X6ConicModel` (added)
from seven leaves: Deligne's `π₀` at level `𝒪̂^×` in printed form (`ShimuraGlue.DeligneComponentsX6Printed`), the
textbook criterion `GeomConnOfAlgClosure` (EGA IV 4.5, Stacks 0389, weakened), T5 (`PkgI2.TorsionStructure`, already
proved in the chain from the textbook field `mumfordTorsionAlgClosed`, `AvSplit.torsionStructure_of_mumford`),
Baba–Granath (`BabaGranathRational`), González–Rotger Thm 5.12 (`GonzalezRotgerX6`), Elkies' equations as charts over
the `t`-line (`ElkiesEquationsX6`), and Shimura reciprocity in ray-class form (`ShimuraGlue.Ray.RayClassCM`, a
consequence of a printed theorem).

As route-a-fold did for the other moduli leaves (`TailZ17`), the five leaves stated on a witness with the kernel's
`R1fpProps` enter the bundles in their abelian-scheme form (`R1fpPropsAb`, the objects of the published fine-moduli
problem): each `LAb` below is the text of `L` with `R1fpProps` replaced by `R1fpPropsAb`, in `L`'s namespace with `L`'s
`open`s, and `L_iff_ab` (under Mumford's rigidity, from the field `mumfordRigidityCore`) closes by rewriting
`R1fpProps = R1fpPropsAb` (`r1fpProps_eq_ab'`), which checks that the two texts elaborate to the same term up to that
one constant. docs/research/x6-fold.md lists the fields.

pi0-fold: the fields `deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure` of `OpenAddedLeaves12` are removed (the
chain carries the weak row `LeafAdopt.R1R2fpRepW`, whose base witness comes from `GonzalezRotgerX6`; TailZ23's
`x6Rows_of_open14`), with this module's off-chain readers `x6Rows_of_open13`, `researchLeaves12_of_open13`,
`addedLeaves11_of_open12` and `sixContactMin_of_open16`. -/

/-! ## The abelian-scheme forms of the five moduli leaves -/

namespace ShimuraGlue

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum
attribute [local instance 2000] instAlgebraAdicCompletion

/-- **Abelian-scheme form of `ShimuraGlue.DeligneComponentsX6Printed`** (Deligne's `π₀` display at level `𝒪̂^×` on
the canonical `X₆`): its text with `R1fpProps` replaced by `R1fpPropsAb`. -/
def DeligneComponentsX6PrintedAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ DelignePi0 X Kfull

end ShimuraGlue

namespace ShimuraGlue.Ray

open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields NumberField IsDedekindDomain
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `ShimuraGlue.Ray.RayClassCM`** (Shimura reciprocity at CM points in ray-class form, a
consequence): its text with `R1fpProps` replaced by `R1fpPropsAb`. -/
def RayClassCMAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      (HasCM4 P.q → Nonempty (residueImage (X := Y.left) y.left →+* rayClassField (mod3 K4))) ∧
      (HasCM3 P.q → Nonempty (residueImage (X := Y.left) y.left →+* rayClassField (mod3 K3))) ∧
      (HasCM24 P.q → Nonempty (residueImage (X := Y.left) y.left →+* rayClassField (mod3 K24)))

end ShimuraGlue.Ray

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.GonzalezRotgerX6`** (González–Rotger 2006 Thm 5.12 on the canonical
`X₆`): its text with `R1fpProps` replaced by `R1fpPropsAb`. -/
def GonzalezRotgerX6Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R5ptProps X Ψ

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.ElkiesEquationsX6`** (Elkies, ANTS-III (1998) §3: `X₆` over the
`t`-line as the charts `s² = −t, r² = 3(t − 1)`, with the fibre and CM clauses): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def ElkiesEquationsX6Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (t : ToP1 X.left),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    (∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
      Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
        (t.val (K := Qbar) x.left = t.val (K := Qbar) x'.left ↔
            ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
    X6Glue.ElkiesCharts X t

section
open scoped Classical

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.BabaGranathRational`** (Baba–Granath 2008 Thm 2.1 and Lemma 3.1
on the canonical `X₆`): its text with `R1fpProps` replaced by `R1fpPropsAb` (stated, like the original, under
`open scoped Classical`). -/
def BabaGranathRationalAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (π : ToP1 X.left)
    (t₄ t₃ t₂₄ : OnePoint ℚ),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ t₄ ≠ t₃ ∧ t₄ ≠ t₂₄ ∧ t₃ ≠ t₂₄ ∧
    ∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
      Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
        (π.val (K := Qbar) x.left = π.val (K := Qbar) x'.left ↔
            ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
        (HasCM4 P.q ↔ π.val (K := Qbar) x.left = t₄.map (algebraMap ℚ Qbar)) ∧
        (HasCM3 P.q ↔ π.val (K := Qbar) x.left = t₃.map (algebraMap ℚ Qbar)) ∧
        (HasCM24 P.q ↔ π.val (K := Qbar) x.left = t₂₄.map (algebraMap ℚ Qbar))

end

end HDec.QMSplit.Moduli

/-! ## Each leaf from its abelian-scheme form, under rigidity -/

namespace LeafQM.AV.R1UnivRigid

theorem deligneComponentsX6Printed_iff_ab (hR : MumfordRigidity) :
    ShimuraGlue.DeligneComponentsX6Printed ↔ ShimuraGlue.DeligneComponentsX6PrintedAb := by
  unfold ShimuraGlue.DeligneComponentsX6Printed ShimuraGlue.DeligneComponentsX6PrintedAb
  rw [r1fpProps_eq_ab' hR]

theorem rayClassCM_iff_ab (hR : MumfordRigidity) :
    ShimuraGlue.Ray.RayClassCM ↔ ShimuraGlue.Ray.RayClassCMAb := by
  unfold ShimuraGlue.Ray.RayClassCM ShimuraGlue.Ray.RayClassCMAb
  rw [r1fpProps_eq_ab' hR]

theorem gonzalezRotgerX6_iff_ab (hR : MumfordRigidity) :
    HDec.QMSplit.Moduli.GonzalezRotgerX6 ↔ HDec.QMSplit.Moduli.GonzalezRotgerX6Ab := by
  unfold HDec.QMSplit.Moduli.GonzalezRotgerX6 HDec.QMSplit.Moduli.GonzalezRotgerX6Ab
  rw [r1fpProps_eq_ab' hR]

theorem elkiesEquationsX6_iff_ab (hR : MumfordRigidity) :
    HDec.QMSplit.Moduli.ElkiesEquationsX6 ↔ HDec.QMSplit.Moduli.ElkiesEquationsX6Ab := by
  unfold HDec.QMSplit.Moduli.ElkiesEquationsX6 HDec.QMSplit.Moduli.ElkiesEquationsX6Ab
  rw [r1fpProps_eq_ab' hR]

theorem babaGranathRational_iff_ab (hR : MumfordRigidity) :
    HDec.QMSplit.Moduli.BabaGranathRational ↔ HDec.QMSplit.Moduli.BabaGranathRationalAb := by
  unfold HDec.QMSplit.Moduli.BabaGranathRational HDec.QMSplit.Moduli.BabaGranathRationalAb
  rw [r1fpProps_eq_ab' hR]

end LeafQM.AV.R1UnivRigid

namespace HDec

namespace HSyn

/-! ## The bundles -/

/-- **The research leaves still open** (x6-fold): leaf-fold12's `OpenResearchLeaves12` without `r1r2Ab` (proved by
x6-glue's `r1r2_of_published`, through `r1R2fpRep_iff_ab`), with four of its leaves added in abelian-scheme form.
35 fields. -/
structure OpenResearchLeaves13 : Prop where
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
  /-- c-to-printed, printed form: Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 4 (over a Dedekind
  domain, a smooth separated model of finite type is a Néron model iff its localizations at the closed points are;
  locator UNVERIFIED). Replaces `neronLocalizesDVR`. -/
  blr_1_2_4 : _root_.CToPrinted.BLR_1_2_4
  /-- c-to-printed, printed form: Faltings 1983, Lemma 5 (the change of the Faltings height under an isogeny
  through `log #s*Ω¹` of its kernel; locator UNVERIFIED). With `raynaudKernelBound` replaces `faltingsLemma5BC`. -/
  faltingsLemma5Printed : _root_.CToPrinted.FaltingsLemma5Printed
  /-- c-to-printed, printed form: Raynaud's bound on the kernel term in Faltings' Lemma 5 (locator UNVERIFIED). -/
  raynaudKernelBound : _root_.CToPrinted.RaynaudKernelBound
  /-- c-to-printed, printed form: SGA 3 VI_B 3.10 (the identity component `G⁰` of a smooth group scheme is open;
  number UNVERIFIED). With the next two and `geomConnOfRationalPoint` replaces `semistableNeronBaseChange`. -/
  sga3_VIB_3_10 : _root_.CToPrinted.SGA3_VIB_3_10
  /-- c-to-printed, printed form: SGA 7 IX 3.3 (`N⁰ ⊗ R' ≅ N'⁰` for semistable reduction; locator UNVERIFIED). -/
  sga7_IX_3_3 : _root_.CToPrinted.SGA7_IX_3_3
  /-- c-to-printed, printed form: EGA IV 8.10.5, open immersions descend through limits (locator UNVERIFIED). -/
  egaIV_8_10_5_openImm : _root_.CToPrinted.EGAIV_8_10_5_openImm
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- x6-glue, printed form (on abelian schemes): Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998),
  §3 (display, section number and the `0`/`∞` orientation UNVERIFIED): `X₆` over the `t`-line is
  `s² = −t, r² = 3(t − 1)` (`X6Glue.ElkiesCharts`), with `t` a coordinate on `X₆/W` and `t = 0, 1, ∞` at the CM
  points of discriminants `−24, −4, −3`. -/
  elkiesEquationsX6Ab : QMSplit.Moduli.ElkiesEquationsX6Ab
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb

/-- **The added leaves still open** (x6-fold): leaf-fold12's `OpenAddedLeaves11` without `x6ConicModel` (proved by
x6-glue's `x6ConicModel_of_published`), with two of its leaves added. 14 fields. -/
structure OpenAddedLeaves12 : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop. 2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- qm-split, H-87/H-88: `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` (Shimura 1971 Prop. 9.2;
  Shimizu 1965). -/
  shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1

/-! ## From the new bundles to leaf-fold12's -/

end HSyn

end HDec

#print axioms HDec.QMSplit.Moduli.r1r2_of_published
#print axioms HDec.QMSplit.Moduli.x6ConicModel_of_published
