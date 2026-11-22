/-
Multiplication-etale construction: LFPFromComposite.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.RingHom.FinitePresentation

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.MulEtale.StacksVendor

universe u

/-- A morphism property defined by a property of ring maps descends along a composite whenever
the corresponding property of ring maps does, after reducing to the affine case. -/
private theorem HasRingHomProperty.of_comp_of
    {P P' : MorphismProperty Scheme.{u}}
    {Q Q' : ∀ {R T : Type u} [CommRing R] [CommRing T], (R →+* T) → Prop}
    [HasRingHomProperty P Q] [HasRingHomProperty P' Q']
    (H : ∀ {R T A : Type u} [CommRing R] [CommRing T] [CommRing A],
      ∀ (a : R →+* T) (b : T →+* A), Q (b.comp a) → Q' a → Q b)
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S} (h : P (f ≫ g)) (hg : P' g) : P f := by
  wlog hS : IsAffine S generalizing X Y S
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top S))]
    intro U
    have hcomp := IsZariskiLocalAtTarget.restrict h U.1; rw [morphismRestrict_comp] at hcomp
    exact this hcomp (IsZariskiLocalAtTarget.restrict hg U.1) inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top Y)]
    intro U
    exact this (by simpa only [morphismRestrict_ι_assoc] using
      HasRingHomProperty.comp_of_isOpenImmersion P (f ⁻¹ᵁ U.1).ι (f ≫ g) h)
      (HasRingHomProperty.comp_of_isOpenImmersion (Q := Q') P' U.1.ι g hg) inferInstance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top X)]
    intro U
    exact this (by simpa only [Category.assoc] using
      HasRingHomProperty.comp_of_isOpenImmersion P U.1.ι (f ≫ g) h) inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := P)] at h ⊢
  rw [HasRingHomProperty.iff_of_isAffine (P := P')] at hg
  exact H _ _ h hg

/-- If `X ⟶ S` is locally of finite presentation and `Y ⟶ S` is locally of finite
type, then a factor `X ⟶ Y` is locally of finite presentation. -/
@[stacks 02FV "part (1)"]
theorem locallyOfFinitePresentation_of_comp {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFinitePresentation (f ≫ g)]
    [LocallyOfFiniteType g] : LocallyOfFinitePresentation f :=
  HasRingHomProperty.of_comp_of
    (P := @LocallyOfFinitePresentation) (P' := @LocallyOfFiniteType)
    (fun a _ h ha ↦ RingHom.FinitePresentation.of_comp_finiteType a h ha)
    (f := f) (g := g) inferInstance inferInstance

end ZInQ.Contrib.MulEtale.StacksVendor
