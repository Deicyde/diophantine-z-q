/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Actual test-map factors through the ORIGINAL diagonal and generic opens.
These are morphism factors, not equality of field-valued points or extra
line-descent assumptions. They feed the native chosen-psi restriction proof.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorChoice

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ZInQ.Contrib.CloudR2NOS.GoodDescent
open ZInQ.Contrib.CloudR2NOS.GoodDescent.GenericModel

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

/-- The actual diagonal equality produces an actual open-factor morphism. -/
theorem exists_equalityOpen_lift
    {U S T T' : Scheme.{u}} (p : U ⟶ S) [Etale p]
    (u₁ u₂ : T ⟶ U) (h : u₁ ≫ p = u₂ ≫ p)
    (t : T' ⟶ T) (he : t ≫ u₁ = t ≫ u₂) :
    ∃ r : T' ⟶ (equalityOpen p u₁ u₂ h).toScheme,
      r ≫ (equalityOpen p u₁ u₂ h).ι = t := by
  let D := equalityOpen p u₁ u₂ h
  have hd : t ≫ pullback.lift u₁ u₂ h = (t ≫ u₁) ≫ pullback.diagonal p := by
    apply pullback.hom_ext
    · simp
    · simpa only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
        Category.comp_id] using he.symm
  have hmem : ∀ a : T', t a ∈ D := by
    intro a
    change (pullback.lift u₁ u₂ h) (t a) ∈ Set.range (pullback.diagonal p)
    refine ⟨(t ≫ u₁) a, ?_⟩
    have ha := congrArg (fun f : T' ⟶ pullback p p => f a) hd
    simpa only [Scheme.Hom.comp_apply] using ha.symm
  exact ⟨intoOpen t D hmem, intoOpen_ι t D hmem⟩

/-- A test whose actual base map is generic factors through the literal preimage open. -/
theorem exists_genericOpen_lift
    {T T' S : Scheme.{u}} (b : T ⟶ S) (V : S.Opens) (t : T' ⟶ T)
    (ht : ∀ a : T', (t ≫ b) a ∈ V) :
    ∃ r : T' ⟶ (b ⁻¹ᵁ V).toScheme, r ≫ (b ⁻¹ᵁ V).ι = t := by
  have hmem : ∀ a : T', t a ∈ b ⁻¹ᵁ V := by
    intro a
    exact ht a
  exact ⟨intoOpen t (b ⁻¹ᵁ V) hmem, intoOpen_ι t (b ⁻¹ᵁ V) hmem⟩

#print axioms exists_equalityOpen_lift
#print axioms exists_genericOpen_lift

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
