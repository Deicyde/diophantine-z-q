import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.DescendedFamily
set_option autoImplicit false

/-!
# Geometric connectedness descends along a surjective base change

We prove `Y3Buzzard.GeomConnLocalOnBase`: in a cartesian square with sides
`fst : P ⟶ B`, `snd : P ⟶ X`, `f : B ⟶ Y`, `q : X ⟶ Y`, if `q` is surjective and `snd` is
geometrically connected, then `f` is geometrically connected.

Argument. Let `K` be a field and `y : Spec K ⟶ Y`. Since `q` is surjective, the fibre product
`X ×_Y Spec K` has a point `p`. Let `L` be its residue field, and let `t : Spec L ⟶ X` and
`e : Spec L ⟶ Spec K` be the induced maps, so `t ≫ q = e ≫ y`. The fibre `P ×_X Spec L` of
`snd` is connected. Pasting cartesian squares shows that `P ×_X Spec L` is the base change of
`B ×_Y Spec K ⟶ Spec K` along `e`. The map `e` is surjective because `Spec K` has exactly one
point, so the canonical map `P ×_X Spec L ⟶ B ×_Y Spec K` is surjective. It is continuous, so
its target is connected.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits

namespace Y3Buzzard

namespace GeomConnDescent

/-- The main step. Given the cartesian square `h`, a map `y : S ⟶ Y` from a scheme with exactly
one point, and a map `t : T ⟶ X` from a nonempty scheme lying over `y` through `e : T ⟶ S`,
connectedness of `P ×_X T` implies connectedness of `B ×_Y S`. -/
theorem connectedSpace_of_cover {P B X Y S T : Scheme.{0}} {fst : P ⟶ B} {snd : P ⟶ X}
    {f : B ⟶ Y} {q : X ⟶ Y} (h : IsPullback fst snd f q) (y : S ⟶ Y) (hU : Unique S)
    (t : T ⟶ X) (e : T ⟶ S) (s₀ : T) (hte : t ≫ q = e ≫ y)
    (hT : ConnectedSpace ↥(pullback snd t : Scheme.{0})) : ConnectedSpace ↥(pullback f y : Scheme.{0}) := by
  -- `e` is surjective: its target has exactly one point and its source is nonempty.
  have he : Surjective e := ⟨fun s => ⟨s₀, (hU.uniq _).trans (hU.uniq s).symm⟩⟩
  -- The outer rectangle `P ×_X T ⟶ P ⟶ B` over `T ⟶ X ⟶ Y` is cartesian.
  have hrect : IsPullback (pullback.fst snd t ≫ fst) (pullback.snd snd t) f (t ≫ q) :=
    (IsPullback.of_hasPullback snd t).paste_horiz h
  have w : (pullback.fst snd t ≫ fst) ≫ f = (pullback.snd snd t ≫ e) ≫ y :=
    hrect.w.trans ((congrArg (fun k => pullback.snd snd t ≫ k) hte).trans
      (Category.assoc _ _ _).symm)
  -- The canonical map `P ×_X T ⟶ B ×_Y S`.
  let cmp : pullback snd t ⟶ pullback f y :=
    pullback.lift (pullback.fst snd t ≫ fst) (pullback.snd snd t ≫ e) w
  have hg1 : cmp ≫ pullback.fst f y = pullback.fst snd t ≫ fst := pullback.lift_fst _ _ _
  have hg2 : cmp ≫ pullback.snd f y = pullback.snd snd t ≫ e := pullback.lift_snd _ _ _
  have hrect' : IsPullback (cmp ≫ pullback.fst f y) (pullback.snd snd t) f (e ≫ y) :=
    Eq.mpr (congrArg (fun k => IsPullback k (pullback.snd snd t) f (e ≫ y)) hg1)
      (Eq.mp (congrArg (fun k => IsPullback (pullback.fst snd t ≫ fst) (pullback.snd snd t) f k)
        hte) hrect)
  -- The left square is cartesian, so `cmp` is a base change of `e`.
  have hleft : IsPullback cmp (pullback.snd snd t) (pullback.snd f y) e :=
    IsPullback.of_right hrect' hg2 (IsPullback.of_hasPullback f y)
  have hcmp : Surjective cmp :=
    MorphismProperty.of_isPullback (P := @Surjective) hleft.flip he
  exact Function.Surjective.connectedSpace (@Surjective.surj _ _ cmp hcmp)
    (Scheme.Hom.continuous cmp)

/-- For `y : S ⟶ Y` with `S` a one-point scheme, the fibre `B ×_Y S` is connected. -/
theorem connectedSpace_of_point {P B X Y S : Scheme.{0}} {fst : P ⟶ B} {snd : P ⟶ X}
    {f : B ⟶ Y} {q : X ⟶ Y} (h : IsPullback fst snd f q) (hq : Surjective q)
    (hgeo : geometrically (fun Z : Scheme.{0} => ConnectedSpace Z) snd) (y : S ⟶ Y)
    (hU : Unique S) : ConnectedSpace ↥(pullback f y : Scheme.{0}) := by
  -- The base change of `q` along `y` is surjective, so `X ×_Y S` has a point `p`.
  have hsq : Surjective (pullback.snd q y) :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback q y) hq
  obtain ⟨p, -⟩ := @Surjective.surj _ _ (pullback.snd q y) hsq (@default _ hU.toInhabited)
  -- A point of `Spec` of the residue field at `p`.
  obtain ⟨s₀⟩ : Nonempty ↥(Spec ((pullback q y).residueField p)) := by
    first
      | exact inferInstance
      | exact ⟨(default : PrimeSpectrum ((pullback q y).residueField p))⟩
  have hte : ((pullback q y).fromSpecResidueField p ≫ pullback.fst q y) ≫ q =
      ((pullback q y).fromSpecResidueField p ≫ pullback.snd q y) ≫ y :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => (pullback q y).fromSpecResidueField p ≫ k) pullback.condition).trans
        (Category.assoc _ _ _).symm)
  -- The fibre of `snd` over the field point is connected.
  have hT : ConnectedSpace
      ↥(pullback snd ((pullback q y).fromSpecResidueField p ≫ pullback.fst q y) : Scheme.{0}) :=
    pullback_of_geometrically hgeo ((pullback q y).residueField p)
      ((pullback q y).fromSpecResidueField p ≫ pullback.fst q y)
  exact connectedSpace_of_cover h y hU _ _ s₀ hte hT

end GeomConnDescent

/-- Geometric connectedness descends along a surjective base change. -/
theorem geomConnLocalOnBase : GeomConnLocalOnBase := by
  intro P B X Y fst snd f q h hq hsnd
  have hgeo : geometrically (fun Z : Scheme.{0} => ConnectedSpace Z) snd :=
    (geometricallyConnected_iff snd).mp hsnd
  refine (geometricallyConnected_iff f).mpr ?_
  refine geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_
  intro K hK y
  -- `Spec K` has exactly one point.
  have hU : Unique (PrimeSpectrum K) := inferInstance
  first
    | exact GeomConnDescent.connectedSpace_of_point h hq hgeo y hU
    | exact GeomConnDescent.connectedSpace_of_point h hq hgeo y
        (inferInstanceAs (Unique (PrimeSpectrum K)))

end Y3Buzzard
