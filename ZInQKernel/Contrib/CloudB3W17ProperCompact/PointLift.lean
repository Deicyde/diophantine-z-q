/-
Copyright (c) 2026 W17 contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace W17ProperCompact

/-- A surjective locally finite type morphism over an algebraically closed field
is surjective on field-valued points. -/
theorem surjective_over_points {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y)
    [LocallyOfFiniteType f.left] [Surjective f.left] :
    Function.Surjective
      (fun P : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X => P ≫ f) := by
  intro P
  let F : Scheme.{u} := pullback f.left P.left
  let t : F ⟶ Spec (CommRingCat.of K) := pullback.snd f.left P.left
  have : LocallyOfFiniteType t := inferInstance
  have : Surjective t := inferInstance
  obtain ⟨z, hz⟩ := t.surjective (IsLocalRing.closedPoint K)
  have : Nonempty F := ⟨z⟩
  have : JacobsonSpace F := LocallyOfFiniteType.jacobsonSpace t
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set F).Nonempty) isClosed_univ.isLocallyClosed
  have hxClosed : IsClosed ({x} : Set F) := hx
  let r : Spec (CommRingCat.of K) ⟶ F := pointOfClosedPoint t x hxClosed
  have hr : r ≫ t = 𝟙 _ := pointOfClosedPoint_comp t x hxClosed
  let q : Spec (CommRingCat.of K) ⟶ X.left := r ≫ pullback.fst f.left P.left
  have hqf : q ≫ f.left = P.left := by
    calc
      q ≫ f.left = r ≫ (pullback.fst f.left P.left ≫ f.left) := Category.assoc _ _ _
      _ = r ≫ (pullback.snd f.left P.left ≫ P.left) :=
        congrArg (r ≫ ·) pullback.condition
      _ = (r ≫ t) ≫ P.left := (Category.assoc _ _ _).symm
      _ = P.left := (congrArg (fun a => a ≫ P.left) hr).trans (Category.id_comp _)
  have hq : q ≫ X.hom = 𝟙 _ := by
    calc
      q ≫ X.hom = q ≫ (f.left ≫ Y.hom) := congrArg (q ≫ ·) (Over.w f).symm
      _ = (q ≫ f.left) ≫ Y.hom := (Category.assoc _ _ _).symm
      _ = P.left ≫ Y.hom := congrArg (· ≫ Y.hom) hqf
      _ = 𝟙 _ := Over.w P
  refine ⟨Over.homMk q hq, ?_⟩
  exact Over.OverMorphism.ext hqf

end W17ProperCompact
