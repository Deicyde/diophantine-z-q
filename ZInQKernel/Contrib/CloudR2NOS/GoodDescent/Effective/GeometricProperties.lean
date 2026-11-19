/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

New actual geometric-connectedness descent on the SAME cartesian scheme.
Arbitrary original universes/characteristics and actual field embeddings
are retained. This is property descent, not model/effectivity existence.
The proof lifts a field test to a residue field of the genuine surjective
base pullback and descends connectedness through its surjective field map.
No geometric-connectedness of the desired downstairs scheme is assumed.
-/
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- Geometric connectedness descends through the ACTUAL cartesian comparison
    along any surjective base morphism. No chosen geometric fibre or closure
    is substituted for the original field-valued test. -/
theorem geometricallyConnected_of_surjective_isPullback
    {X X' S S' : Scheme.{u}} {q : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {p : S' ⟶ S}
    (hp : IsPullback q f' f p) [Surjective p] [GeometricallyConnected f'] :
    GeometricallyConnected f := by
  constructor
  intro K instK y Z a b hz
  let T : Scheme.{u} := pullback p y
  let t : T := Classical.choose ((pullback.snd p y).surjective (default : Spec (CommRingCat.of K)))
  let E := T.residueField t
  let k : Spec E ⟶ Spec (CommRingCat.of K) := T.fromSpecResidueField t ≫ pullback.snd p y
  let r : Spec E ⟶ S' := T.fromSpecResidueField t ≫ pullback.fst p y
  have hkr : r ≫ p = k ≫ y := by
    simpa only [r, k, Category.assoc] using
      congrArg (T.fromSpecResidueField t ≫ ·) (pullback.condition (f := p) (g := y))
  haveI : Surjective k := by
    constructor
    intro z
    let z' : Spec E := default
    exact ⟨z', Subsingleton.elim _ _⟩
  let B : Scheme.{u} := pullback f' r
  haveI : ConnectedSpace B :=
    (inferInstance : GeometricallyConnected f').geometrically_connectedSpace r
      (pullback.fst f' r) (pullback.snd f' r) (IsPullback.of_hasPullback f' r)
  have hfull : IsPullback (pullback.fst f' r ≫ q) (pullback.snd f' r) f (k ≫ y) := by
    have h := (IsPullback.of_hasPullback f' r).paste_horiz hp
    rwa [hkr] at h
  let d : B ⟶ Z := hz.lift (pullback.fst f' r ≫ q) (pullback.snd f' r ≫ k)
    (hfull.w.trans (Category.assoc (pullback.snd f' r) k y).symm)
  have hd : IsPullback d (pullback.snd f' r) b k := IsPullback.of_right' hfull hz
  haveI : Surjective d := MorphismProperty.of_isPullback hd.flip inferInstance
  exact d.surjective.connectedSpace d.continuous

/-- Smoothness also descends through the SAME cartesian comparison, using
    the genuine Mathlib fpqc descent proof rather than a supplied Smooth Fact. -/
theorem smooth_of_fpqc_isPullback
    {X X' S S' : Scheme.{u}} {q : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {p : S' ⟶ S}
    (hp : IsPullback q f' f p) [Surjective p] [Flat p] [QuasiCompact p] [Smooth f'] : Smooth f :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

#print axioms geometricallyConnected_of_surjective_isPullback
#print axioms smooth_of_fpqc_isPullback

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
