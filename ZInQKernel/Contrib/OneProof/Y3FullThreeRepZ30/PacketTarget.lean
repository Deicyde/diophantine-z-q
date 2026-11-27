import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.G0Equiv
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
open Y3Fix.G0Dictionary
open SGRSplit
namespace Y3Buzzard

/-!
# The level-three representability target as an abstract packet (draft)

`Y3Packet` packages a proper smooth curve `Y` over `Z[1/30]` carrying a false elliptic curve
`E` with a section `P` generating its full level-three structure, such that `(E, P)` is
universal among false elliptic curves with a level-three generator over `Z[1/30]`-schemes.
Such a packet proves the repository target `Y3RouteA.Y3FullThreeRepZ30`, because a
level-three family is a false elliptic curve with the generator `eta 1`, and base change of
families is base change of the curve carrying `eta 1`.
Source: Buzzard 1997, Section 1, Def. 1.1 (a full level structure is determined by the image
of 1 by `O`-linearity).
-/

/-- A fine moduli curve for false elliptic curves with a full level-three generator over
`Z[1/30]`, stated with the universal pair `(E, P)`. -/
structure Y3Packet where
  Y : Over Z30Base
  E : FEC Y.left
  P : Y.left ⟶ E.F.left
  sec : P ≫ E.F.hom = 𝟙 _
  gen : IsGen 3 E P
  proper : IsProper Y.hom
  smooth : SmoothOfRelativeDimension 1 Y.hom
  rep : ∀ (S : Over Z30Base) (A' : FEC S.left) (P3' : S.left ⟶ A'.F.left),
    P3' ≫ A'.F.hom = 𝟙 S.left → IsGen 3 A' P3' →
      ∃! g : S ⟶ Y, ∃ h : A'.F.left ⟶ E.F.left,
        IsPullback h A'.F.hom E.F.hom g.left ∧
        (∀ a : O, A'.iota a ≫ h = h ≫ E.iota a) ∧
        P3' ≫ h = g.left ≫ P

/-- The section `eta 1` of the family built from the packet is `P`. -/
theorem packet_eta_one (K : Y3Packet) : (ofFECGen K.E K.P K.sec K.gen).eta 1 = K.P := by
  first
    | exact (ofFECGen_eta K.E K.P K.sec K.gen 1).trans
        ((congrArg (fun f : K.E.F.left ⟶ K.E.F.left => K.P ≫ f) K.E.iota_one).trans
          (Category.comp_id K.P))
    | (show K.P ≫ K.E.iota 1 = K.P
       rw [K.E.iota_one, Category.comp_id])

/-- The base-change condition against the family built from the packet, read on `(E, P)`. -/
theorem packet_cond_iff (K : Y3Packet) {S : Scheme.{0}} (g : S ⟶ K.Y.left)
    (𝒜' : Y3Fix.QMAbSchemeP S) :
    (∃ h : 𝒜'.F.left ⟶ (ofFECGen K.E K.P K.sec K.gen).F.left,
        IsPullback h 𝒜'.F.hom (ofFECGen K.E K.P K.sec K.gen).F.hom g ∧
        (∀ a : O, 𝒜'.iota a ≫ h = h ≫ (ofFECGen K.E K.P K.sec K.gen).iota a) ∧
        𝒜'.eta 1 ≫ h = g ≫ (ofFECGen K.E K.P K.sec K.gen).eta 1) ↔
      ∃ h : 𝒜'.F.left ⟶ K.E.F.left, IsPullback h 𝒜'.F.hom K.E.F.hom g ∧
        (∀ a : O, 𝒜'.iota a ≫ h = h ≫ K.E.iota a) ∧ 𝒜'.eta 1 ≫ h = g ≫ K.P := by
  have hη : g ≫ (ofFECGen K.E K.P K.sec K.gen).eta 1 = g ≫ K.P :=
    congrArg (fun f : K.Y.left ⟶ K.E.F.left => g ≫ f) (packet_eta_one K)
  constructor
  · rintro ⟨h, hpb, hι, h1⟩
    exact ⟨h, hpb, hι, h1.trans hη⟩
  · rintro ⟨h, hpb, hι, h1⟩
    exact ⟨h, hpb, hι, h1.trans hη.symm⟩

/-- A universal packet for false elliptic curves with a full level-three generator proves the
level-three representability target over `Z[1/30]`. -/
theorem y3FullThreeRepZ30_of_packet (K : Y3Packet) : Y3RouteA.Y3FullThreeRepZ30 := by
  unfold Y3RouteA.Y3FullThreeRepZ30
  refine ⟨K.Y, ofFECGen K.E K.P K.sec K.gen, K.proper, K.smooth, ?_⟩
  intro S _ 𝒜'
  -- The generator triple of `𝒜'`: the curve `𝒜'.toFEC` with the section `eta 1`.
  have hrep0 := K.rep S (toFECGen 𝒜').A (toFECGen 𝒜').P (toFECGen 𝒜').sec (toFECGen 𝒜').gen
  have hrep : ∃! g : S ⟶ K.Y, ∃ h : 𝒜'.F.left ⟶ K.E.F.left,
      IsPullback h 𝒜'.F.hom K.E.F.hom g.left ∧
      (∀ a : O, 𝒜'.iota a ≫ h = h ≫ K.E.iota a) ∧ 𝒜'.eta 1 ≫ h = g.left ≫ K.P := hrep0
  first
    | exact (existsUnique_congr fun g : S ⟶ K.Y =>
        (qmFamFibre_iff (ofFECGen K.E K.P K.sec K.gen) g.left 𝒜').trans
          (packet_cond_iff K g.left 𝒜')).2 hrep
    | (obtain ⟨g, hg, huniq⟩ := hrep
       exact ⟨g,
         ((qmFamFibre_iff (ofFECGen K.E K.P K.sec K.gen) g.left 𝒜').trans
           (packet_cond_iff K g.left 𝒜')).2 hg,
         fun g' hg' => huniq g'
           (((qmFamFibre_iff (ofFECGen K.E K.P K.sec K.gen) g'.left 𝒜').trans
             (packet_cond_iff K g'.left 𝒜')).1 hg')⟩)

end Y3Buzzard
