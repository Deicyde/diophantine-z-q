import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Effective epimorphisms for the integral Y3 quotients

A finite, flat, surjective morphism of schemes is an effective epimorphism, by the
fpqc instance in Mathlib. If `A` is the pullback of `b` along `qX`, then the induced
map of fibre squares `A ×_X A ⟶ B ×_Y B` is a base change of `qX`. It therefore
inherits finiteness, flatness and surjectivity, and is again an effective
epimorphism.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Y3QuotientDescent

section FibreSquare

variable {C : Type u} [Category.{v} C]

/-- The side condition for the induced map of fibre squares. -/
theorem fibreSquare_w {A B X Y : C} {qA : A ⟶ B} {p : A ⟶ X} {b : B ⟶ Y}
    {qX : X ⟶ Y} [HasPullback p p] (hw : qA ≫ b = p ≫ qX) :
    (pullback.fst p p ≫ qA) ≫ b = (pullback.snd p p ≫ qA) ≫ b := by
  rw [Category.assoc, Category.assoc, hw, ← Category.assoc, pullback.condition,
    Category.assoc]

/-- The induced map of fibre squares is the base change of `qX` along
`B ×_Y B ⟶ Y`. -/
theorem isPullback_fibreSquare {A B X Y : C} {qA : A ⟶ B} {p : A ⟶ X} {b : B ⟶ Y}
    {qX : X ⟶ Y} [HasPullback p p] [HasPullback b b] (h : IsPullback qA p b qX)
    (w : (pullback.fst p p ≫ qA) ≫ b = (pullback.snd p p ≫ qA) ≫ b) :
    IsPullback (pullback.lift (pullback.fst p p ≫ qA) (pullback.snd p p ≫ qA) w)
      (pullback.fst p p ≫ p) (pullback.fst b b ≫ b) qX := by
  have hout : IsPullback (pullback.snd p p ≫ qA) (pullback.fst p p) b (p ≫ qX) :=
    (IsPullback.of_hasPullback p p).flip.paste_horiz h
  have htop : IsPullback (pullback.lift (pullback.fst p p ≫ qA) (pullback.snd p p ≫ qA) w)
      (pullback.fst p p) (pullback.fst b b) qA := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback b b).flip
    rw [pullback.lift_snd, h.w]
    exact hout
  exact htop.paste_vert h

end FibreSquare

section Schemes

open AlgebraicGeometry

/-- Finite, flat and surjective morphisms of schemes are effective epimorphisms. -/
theorem effectiveEpi_of_isFinite {X Y : Scheme.{u}} (q : X ⟶ Y) [IsFinite q] [Flat q]
    [Surjective q] : EffectiveEpi q :=
  inferInstance

/-- The induced map of fibre squares is finite, flat and surjective when `qX` is. -/
theorem fibreSquare_properties {A B X Y : Scheme.{u}} {qA : A ⟶ B} {p : A ⟶ X}
    {b : B ⟶ Y} {qX : X ⟶ Y} [IsFinite qX] [Flat qX] [Surjective qX]
    (h : IsPullback qA p b qX) :
    IsFinite (pullback.lift (pullback.fst p p ≫ qA) (pullback.snd p p ≫ qA)
        (fibreSquare_w h.w)) ∧
      Flat (pullback.lift (pullback.fst p p ≫ qA) (pullback.snd p p ≫ qA)
        (fibreSquare_w h.w)) ∧
      Surjective (pullback.lift (pullback.fst p p ≫ qA) (pullback.snd p p ≫ qA)
        (fibreSquare_w h.w)) := by
  have sq := (isPullback_fibreSquare h (fibreSquare_w h.w)).flip
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) sq ‹_›,
    MorphismProperty.of_isPullback (P := @Flat) sq ‹_›,
    MorphismProperty.of_isPullback (P := @Surjective) sq ‹_›⟩

/-- Hence the induced map of fibre squares is an effective epimorphism. -/
theorem effectiveEpi_fibreSquare {A B X Y : Scheme.{u}} {qA : A ⟶ B} {p : A ⟶ X}
    {b : B ⟶ Y} {qX : X ⟶ Y} [IsFinite qX] [Flat qX] [Surjective qX]
    (h : IsPullback qA p b qX) :
    EffectiveEpi (pullback.lift (pullback.fst p p ≫ qA) (pullback.snd p p ≫ qA)
      (fibreSquare_w h.w)) := by
  obtain ⟨h₁, h₂, h₃⟩ := fibreSquare_properties h
  exact @effectiveEpi_of_isFinite _ _ _ h₁ h₂ h₃

end Schemes

end Y3QuotientDescent
