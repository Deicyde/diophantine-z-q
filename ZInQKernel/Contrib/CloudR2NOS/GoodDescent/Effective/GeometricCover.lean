/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Geometric connectedness on the SAME descended scheme from actual generic
and closed fibres. No geometric-connectedness of the finite étale stage
is assumed or spread. The point-cover is used ONLY to select a genuine
residue-field-valued pullback test; connectedness is proved for EVERY
field-valued test on its actual cartesian fibre, not inferred from point
cardinality or used to manufacture the earlier whole-fibre Mono claim.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GeometricProperties
import Mathlib.AlgebraicGeometry.PullbackCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- Geometric connectedness descends from a point-covering family of ACTUAL
    cartesian base changes. Every upstairs connectedness test and field map
    is constructed by the native scheme pullback/residue-field API. -/
theorem geometricallyConnected_of_cover_isPullbacks
    {I : Type v} {X S : Scheme.{u}} (f : X ⟶ S)
    (U Y : I → Scheme.{u}) (p : ∀ i, U i ⟶ S)
    (q : ∀ i, Y i ⟶ X) (g : ∀ i, Y i ⟶ U i)
    (hc : ∀ i, IsPullback (q i) (g i) f (p i))
    (hCover : ∀ s : S, ∃ i, ∃ t : U i, p i t = s)
    [hg : ∀ i, GeometricallyConnected (g i)] : GeometricallyConnected f := by
  constructor
  intro K instK y Z a b hz
  let z : Spec (CommRingCat.of K) := default
  obtain ⟨i, t, ht⟩ := hCover (y z)
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := p i) (g := y) t z ht
  let T : Scheme.{u} := pullback (p i) y
  let E := T.residueField w
  let k : Spec E ⟶ Spec (CommRingCat.of K) := T.fromSpecResidueField w ≫ pullback.snd (p i) y
  let r : Spec E ⟶ U i := T.fromSpecResidueField w ≫ pullback.fst (p i) y
  have hkr : r ≫ p i = k ≫ y := by
    simpa only [r, k, Category.assoc] using
      congrArg (T.fromSpecResidueField w ≫ ·) (pullback.condition (f := p i) (g := y))
  haveI : Surjective k := by
    constructor
    intro z'
    exact ⟨(default : Spec E), Subsingleton.elim _ _⟩
  let B : Scheme.{u} := pullback (g i) r
  haveI : ConnectedSpace B := (hg i).geometrically_connectedSpace r
    (pullback.fst (g i) r) (pullback.snd (g i) r) (IsPullback.of_hasPullback (g i) r)
  have hfull : IsPullback (pullback.fst (g i) r ≫ q i) (pullback.snd (g i) r) f (k ≫ y) := by
    have h := (IsPullback.of_hasPullback (g i) r).paste_horiz (hc i)
    rwa [hkr] at h
  let d : B ⟶ Z := hz.lift (pullback.fst (g i) r ≫ q i) (pullback.snd (g i) r ≫ k)
    (hfull.w.trans (Category.assoc (pullback.snd (g i) r) k y).symm)
  have hd : IsPullback d (pullback.snd (g i) r) b k := IsPullback.of_right' hfull hz
  haveI : Surjective d := MorphismProperty.of_isPullback hd.flip inferInstance
  exact d.surjective.connectedSpace d.continuous

/-- Original generic open and closed residue fibre suffice on a trait.
    This does not assume geometric connectedness of the étale stage.
    The original closed residue map is compared in ResiduePoint, not replaced
    by a strict/separable residue extension or a one-topological-point Mono. -/
theorem geometricallyConnected_of_generic_closed_isPullbacks
    {X S Xg Xc : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) (c : S)
    (hV : ∀ z : S, z ∉ V → z = c)
    (qg : Xg ⟶ X) (fg : Xg ⟶ V.toScheme) (hg : IsPullback qg fg f V.ι)
    (qc : Xc ⟶ X) (fc : Xc ⟶ Spec (S.residueField c))
    (hc : IsPullback qc fc f (S.fromSpecResidueField c))
    [GeometricallyConnected fg] [GeometricallyConnected fc] : GeometricallyConnected f := by
  let U : Bool → Scheme.{u} := fun b => if b then Spec (S.residueField c) else V.toScheme
  let Y : Bool → Scheme.{u} := fun b => if b then Xc else Xg
  let p : ∀ b, U b ⟶ S := fun b => by
    cases b
    · exact V.ι
    · exact S.fromSpecResidueField c
  let q : ∀ b, Y b ⟶ X := fun b => by
    cases b
    · exact qg
    · exact qc
  let g : ∀ b, Y b ⟶ U b := fun b => by
    cases b
    · exact fg
    · exact fc
  have hp : ∀ b, IsPullback (q b) (g b) f (p b) := by
    intro b
    cases b
    · exact hg
    · exact hc
  have hCover : ∀ s : S, ∃ b, ∃ t : U b, p b t = s := by
    intro s
    by_cases hs : s ∈ V
    · exact ⟨false, ⟨s, hs⟩, rfl⟩
    · have he : s = c := hV s hs
      have hc' : c ∈ Set.range (S.fromSpecResidueField c) := by
        rw [S.range_fromSpecResidueField c]
        exact Set.mem_singleton c
      obtain ⟨t, ht⟩ := hc'
      exact ⟨true, t, ht.trans he.symm⟩
  haveI : ∀ b, GeometricallyConnected (g b) := by
    intro b
    cases b
    · exact inferInstance
    · exact inferInstance
  exact geometricallyConnected_of_cover_isPullbacks f U Y p q g hp hCover

#print axioms geometricallyConnected_of_cover_isPullbacks
#print axioms geometricallyConnected_of_generic_closed_isPullbacks

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
