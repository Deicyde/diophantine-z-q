import ZInQKernel.Contrib.OneProof.BuzzardXDV15
import ZInQKernel.Contrib.OneProof.SerreRigidityZ30
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.Quotients

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# The level-three moduli target from affine neighbourhoods of finite sets in `A1`

Let `X₁` be the fine moduli scheme of false elliptic curves with `V₁(5)`-structure over
`Z[1/30]` and `A1 = (leafD hB1).A` its universal false elliptic curve. The projectivity input
`ProjectiveFEC` enters the proof of `Y3RouteA.Y3FullThreeRepZ30` only through `fsa_A1`: a closed
immersion of the total space of `A1` into some projective space shows that every finite set of
points of that total space lies in a single affine open
(`Y3QuotientDescent.FiniteSetsInAffines`). This property passes to the total spaces of the
level-5 and level-(5,3) moduli data (`fsa_A5`, `fsa_A35`), where it is used to form the quotient
by `G 5`.

Each declaration below, with the suffix `_fsa`, repeats the proof of its counterpart along the
chain to `Y3RouteA.Y3FullThreeRepZ30`, with the hypothesis
`hA1 : Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left` in place of `ProjectiveFEC`.
-/

attribute [local instance] FEC.grp

/-! ## 1. Finite sets in affines for the total spaces -/

/-- Every finite set of points of the total space of the level-5 moduli datum lies in an affine
open, if the same holds for the total space of `A1`. -/
theorem fsa_A5_fsa (hB1 : BuzzardThm21Cor23V15')
    (hA1 : Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left)
    (hB25 : BuzzardFrameRepTorsor 5) :
    Y3QuotientDescent.FiniteSetsInAffines (moduli5 hB1 hB25).A.F.left :=
  fsa_moduli5Of_A (leafD hB1).X (leafD hB1).A (leafD hB1).α (leafD hB1).ex (leafD hB1).uniq
    (leafF5 hB1 hB25).Z (leafF5 hB1 hB25).i (leafF5 hB1 hB25).mono (leafF5 hB1 hB25).char
    (frameData_isFinite hB25 (leafD hB1).X (leafD hB1).A) hA1

/-- Every finite set of points of the total space of the level-(5,3) moduli datum lies in an
affine open, if the same holds for the total space of `A1`. -/
theorem fsa_A35_fsa (hB1 : BuzzardThm21Cor23V15')
    (hA1 : Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left)
    (hB25 : BuzzardFrameRepTorsor 5) (hB23 : BuzzardFrameRepNS 3) :
    Y3QuotientDescent.FiniteSetsInAffines (moduli35 (moduli5 hB1 hB25) hB23).A.F.left :=
  fsa_moduli35Of_A (moduli5 hB1 hB25) (leafF3 hB1 hB25 hB23).i (leafF3 hB1 hB25 hB23).mono
    (leafF3 hB1 hB25 hB23).char
    (frameRepNS_isFinite hB23 (moduli5 hB1 hB25).X (moduli5 hB1 hB25).A)
    (fsa_A5_fsa hB1 hA1 hB25)

/-! ## 2. The quotient by `G 5` and its properness and smoothness -/

/-- The quotient data of the level-(5,3) datum built from the leaves, with `hA1` in place of
`ProjectiveFEC`. -/
def quotientDataOfLeaves_z30_fsa (hB1 : BuzzardThm21Cor23V15')
    (hA1 : Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left)
    (hB25 : BuzzardFrameRepTorsor 5) (hB23 : BuzzardFrameRepNS 3) (hSR : SerreRigidityFibreZ30)
    (hBC : FECGeomFibre) : QuotientData (moduli35 (moduli5 hB1 hB25) hB23) :=
  quotientData _ (hfix_z30 _ hSR hBC) (fsa_X35 hB1 hB25 hB23) (fsa_A35_fsa hB1 hA1 hB25 hB23)

/-- The quotient `Y` of the level-(5,3) moduli scheme by `G 5`, for the quotient datum built from
the leaves with `hA1`, is proper and smooth of relative dimension 1 over `Z[1/30]`. -/
theorem Y_proper_smooth_z30_fsa (hB1 : BuzzardThm21Cor23V15')
    (hA1 : Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left)
    (hB25 : BuzzardFrameRepTorsor 5) (hB23 : BuzzardFrameRepNS 3) (hSR : SerreRigidityFibreZ30)
    (hBC : FECGeomFibre) (hT5 : TorsionRep 5)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale)
    (hCI : DescentClosedImmersion) (hPM : ProperMonoIsClosedImmersion)
    (hEt : AlgebraicGeometry.Etale (quotientDataOfLeaves_z30_fsa hB1 hA1 hB25 hB23 hSR hBC).qX) :
    IsProper (quotientDataOfLeaves_z30_fsa hB1 hA1 hB25 hB23 hSR hBC).YOver.hom ∧
      SmoothOfRelativeDimension 1
        (quotientDataOfLeaves_z30_fsa hB1 hA1 hB25 hB23 hSR hBC).YOver.hom :=
  Y_proper_smooth_of hB1 hB25 hB23 hT5 hB7b hCI hPM _ hEt

/-! ## 3. The packet -/

/-- The packet built from the leaves it uses, with `hA1` in place of `ProjectiveFEC`. This is a
construction (the packet is data). -/
def y3Packet_of_parts_z30_fsa (hB1 : BuzzardThm21Cor23V15')
    (hA1 : Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left)
    (hB23 : BuzzardFrameRepNS 3) (hB25 : BuzzardFrameRepTorsor 5) (hSR : SerreRigidityFibreZ30)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale)
    (hCI : DescentClosedImmersion) (hT5 : TorsionRep 5)
    (hPM : ProperMonoIsClosedImmersion) (hP : ProperLocalOnBase)
    (hG : GeomConnLocalOnBase) (hD : IsGenDescentFin3)
    (hmul : ActionMulCompatLN) : Y3Packet := by
  let M : Moduli35 := moduli35 (moduli5 hB1 hB25) hB23
  let Q : QuotientData M := quotientDataOfLeaves_z30_fsa hB1 hA1 hB25 hB23 hSR fecGeomFibre
  have hLN : IsLocallyNoetherian M.X.left := isLocallyNoetherian_X35 hB1 hB25 hB23
  let D : DescentInput M.X.left Q.Y := descentInputOf M Q (hmul M Q hLN)
  have hps : IsProper Q.YOver.hom ∧ SmoothOfRelativeDimension 1 Q.YOver.hom :=
    Y_proper_smooth_z30_fsa hB1 hA1 hB25 hB23 hSR fecGeomFibre hT5 hB7b hCI hPM (etale_qX M Q)
  have hYLN : IsLocallyNoetherian Q.Y := isLocallyNoetherian_of_proper_Z30 Q.YOver hps.1
  have hS : SmoothOfRelativeDimension 2 D.b := smooth_b_of_B7b hB7b D hYLN (etale_qX M Q)
  have hrep := rep3 hB25 Q D hP hS hG rfl rfl
    (fun d τ hτ => by
      obtain rfl := eq_of_heq hτ
      exact act_comp_eq (ρA M) Q.kpA d)
    HEq.rfl
  have hsec : D.descP3 ≫ (D.descFEC hP hS hG).F.hom = 𝟙 Q.YOver.left := D.descP3_sec
  have hgen : IsGen 3 (D.descFEC hP hS hG) D.descP3 := by
    have h1 : IsGen 3 (D.descFEC hP hS hG) (D.P3 ≫ D.qA) :=
      (isGen_iff_of_fibre (A := D.descFEC hP hS hG) (A' := D.A) (g := D.qX) (h := D.qA)
        D.hpb (fun a => (D.qA_iotaB a).symm)).1 D.P3_gen
    have h2 : IsGen 3 (D.descFEC hP hS hG) (D.qX ≫ D.descP3) :=
      (congrArg (fun P => IsGen 3 (D.descFEC hP hS hG) P) D.P3_qA).mp h1
    have : Epi D.qX := inferInstance
    exact hD _ (D.descFEC hP hS hG) _ _ D.qX D.descP3 D.finite D.surj inferInstance h2
  exact ⟨Q.YOver, D.descFEC hP hS hG, D.descP3, hsec, hgen, hps.1, hps.2, hrep⟩

/-! ## 4. The level-three moduli target -/

/-- `Y3RouteA.Y3FullThreeRepZ30` from the printed leaves it uses, with `hA1` in place of
`ProjectiveFEC`. -/
theorem y3FullThreeRepZ30_of_printed_z30_fsa (hB1 : BuzzardThm21Cor23V15')
    (hA1 : Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left)
    (hB23 : BuzzardFrameRepNS 3) (hB25 : BuzzardFrameRepTorsor 5)
    (hSR : SerreRigidityFibreZ30) (hB4 : ZeroPreservingIsHomLN)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale)
    (hCI : DescentClosedImmersion) (hM : MilneProp207 5) (hP : ProperLocalOnBase) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_packet
    (y3Packet_of_parts_z30_fsa hB1 hA1 hB23 hB25 hSR hB7b hCI (torsionRep5_of_milne hM)
      properMonoIsClosedImmersion hP geomConnLocalOnBase isGenDescentFin3
      (actionMulCompatLN_of_B4 hB4))

/-- `Y3RouteA.Y3FullThreeRepZ30` from the remaining printed leaves and `hA1`, with properness
descent and descent of closed immersions proved from flat descent. -/
theorem y3FullThreeRepZ30_of_printed_min_z30_fsa (hB1 : BuzzardThm21Cor23V15')
    (hA1 : Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left)
    (hB23 : BuzzardFrameRepNS 3) (hB25 : BuzzardFrameRepTorsor 5)
    (hSR : SerreRigidityFibreZ30) (hB4 : ZeroPreservingIsHomLN)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale) (hM : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_z30_fsa hB1 hA1 hB23 hB25 hSR hB4 hB7b descentClosedImmersion hM
    properLocalOnBase

/-- `Y3RouteA.Y3FullThreeRepZ30` from seven printed inputs and `hA1`, with level-3 frames from
Milne's count of the 3-torsion (`GeomCard3`) and Milne, Prop. 20.7 at `n = 3`. -/
theorem y3FullThreeRepZ30_of_printed_min5_z30_fsa (hB1 : BuzzardThm21Cor23V15')
    (hA1 : Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left)
    (hM3 : MilneProp207 3) (hC3 : GeomCard3) (hB25 : BuzzardFrameRepTorsor 5)
    (hSR : SerreRigidityFibreZ30) (hB4 : ZeroPreservingIsHomLN)
    (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_min_z30_fsa hB1 hA1
    (frameRepNS3_of hM3 hC3 Y3OrderMod.card_OMod3) hB25 hSR hB4
    SourceDescent.h1StdEt_descentSmoothRelDimFiniteEtale hM5

/-- `Y3RouteA.Y3FullThreeRepZ30` from seven printed inputs and `hA1`, with Milne's count of the
5-torsion (`GeomCard5`) in place of `BuzzardFrameRepTorsor 5`. -/
theorem y3FullThreeRepZ30_of_printed_milne5_z30_fsa (hB1 : BuzzardThm21Cor23V15')
    (hA1 : Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left)
    (hM3 : MilneProp207 3) (hC3 : GeomCard3) (hC5 : GeomCard5)
    (hSR : SerreRigidityFibreZ30) (hB4 : ZeroPreservingIsHomLN)
    (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_min5_z30_fsa hB1 hA1 hM3 hC3
    (buzzardFrameRepTorsor5_of_milne hM5 hC5) hSR hB4 hM5

/-- `Y3RouteA.Y3FullThreeRepZ30` from six printed inputs and `hA1`: Milne's Remark 8.4 for every
order prime to the characteristic (`MilneRem84`) gives both counts `GeomCard3` and `GeomCard5`,
and rigidity at level three enters only on geometric fibres over `Z[1/30]`. -/
theorem y3FullThreeRepZ30_of_printed_rem84_z30_fsa (hB1 : BuzzardThm21Cor23V15')
    (hA1 : Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left)
    (hM3 : MilneProp207 3) (hR : MilneRem84) (hSR : SerreRigidityFibreZ30)
    (hB4 : ZeroPreservingIsHomLN) (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_milne5_z30_fsa hB1 hA1 hM3 (geomCard3_of_rem84 hR)
    (geomCard5_of_rem84 hR) hSR hB4 hM5

/-- `Y3RouteA.Y3FullThreeRepZ30` from seven printed inputs and `hA1`: Buzzard's Lemma 2.2 and
Milne's Theorem 12.5 in place of `SerreRigidityLevel3'`. -/
theorem y3FullThreeRepZ30_of_printed_buzzard22_fsa (hB1 : BuzzardThm21Cor23V15')
    (hA1 : Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left)
    (hM3 : MilneProp207 3) (hR : MilneRem84) (hBz : BuzzardLemma22Full5) (hMl : MilneThm125Pts)
    (hB4 : ZeroPreservingIsHomLN) (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_rem84_z30_fsa hB1 hA1 hM3 hR
    (serreRigidityFibreZ30_of_printed hBz hMl hR hB4) hB4 hM5

/-- `Y3RouteA.Y3FullThreeRepZ30` from seven printed inputs, with Buzzard's literal Thm 2.1 and
Cor. 2.3 at `V₁(5)` in place of `BuzzardThm21Cor23V15'`, and the hypothesis that, for the
moduli datum of every proof of `BuzzardThm21Cor23V15'`, every finite set of points of the total
space of the universal false elliptic curve lies in an affine open, in place of
`ProjectiveFEC`. -/
theorem y3FullThreeRepZ30_of_printed_xdv15_fsa (hL : XDV15.BuzzardXDV15Lit) (hM3 : MilneProp207 3)
    (hR : MilneRem84) (hBz : BuzzardLemma22Full5) (hMl : MilneThm125Pts)
    (hB4 : ZeroPreservingIsHomLN)
    (hA1 : ∀ hB1 : BuzzardThm21Cor23V15', Y3QuotientDescent.FiniteSetsInAffines (leafD hB1).A.F.left)
    (hM5 : MilneProp207 5) : Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_buzzard22_fsa (b1Prime_of_literal hL hM5 (geomCard5_of_rem84 hR))
    (hA1 _) hM3 hR hBz hMl hB4 hM5

end Y3Buzzard
