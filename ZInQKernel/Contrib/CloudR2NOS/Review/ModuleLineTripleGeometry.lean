/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Actual triple diagonal/generic test cover. The chart-base equalities are
actual scheme maps, and the cover is derived from the WHOLE residue fibre.
No line cocycle is an input or conclusion of this geometry lemma.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorGenericTests

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.CloudR2NOS.GoodDescent
open ZInQ.Contrib.CloudR2NOS.GoodDescent.GenericModel

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

/-- The intersection of the actual 12/23 equality opens plus the common original
base generic open covers every triple test; no residue-field point shortcut. -/
theorem triple_diagonal_sup_generic
    {U S T : Scheme.{u}} (p : U ⟶ S) [Etale p]
    (c : S) [Mono (p.fiberToSpecResidueField c)] (V : S.Opens)
    (hV : ∀ z : S, z ∉ V → z = c)
    (u₁ u₂ u₃ : T ⟶ U) (h₁₂ : u₁ ≫ p = u₂ ≫ p) (h₂₃ : u₂ ≫ p = u₃ ≫ p) :
    (equalityOpen p u₁ u₂ h₁₂ ⊓ equalityOpen p u₂ u₃ h₂₃) ⊔
      (u₁ ≫ p) ⁻¹ᵁ V = ⊤ := by
  have h₁ := equality_sup_generic_eq_top p c V hV u₁ u₂ h₁₂
  have h₂ := equality_sup_generic_eq_top p c V hV u₂ u₃ h₂₃
  have hG : (u₂ ≫ p) ⁻¹ᵁ V = (u₁ ≫ p) ⁻¹ᵁ V :=
    congrArg (fun f : T ⟶ S => f ⁻¹ᵁ V) h₁₂.symm
  rw [hG] at h₂
  rw [sup_inf_right, h₁, h₂]
  simp

/-- Each actual pair-base equality holds on the intersection open. -/
theorem triple_diagonal_base_eq
    {U S T : Scheme.{u}} (p : U ⟶ S) [Etale p]
    (u₁ u₂ u₃ : T ⟶ U) (h₁₂ : u₁ ≫ p = u₂ ≫ p) (h₂₃ : u₂ ≫ p = u₃ ≫ p) :
    let D := equalityOpen p u₁ u₂ h₁₂ ⊓ equalityOpen p u₂ u₃ h₂₃
    D.ι ≫ u₁ = D.ι ≫ u₂ ∧ D.ι ≫ u₂ = D.ι ≫ u₃ := by
  let D := equalityOpen p u₁ u₂ h₁₂ ⊓ equalityOpen p u₂ u₃ h₂₃
  let r₁ : D.toScheme ⟶ (equalityOpen p u₁ u₂ h₁₂).toScheme := T.homOfLE inf_le_left
  let r₂ : D.toScheme ⟶ (equalityOpen p u₂ u₃ h₂₃).toScheme := T.homOfLE inf_le_right
  have hr₁ : r₁ ≫ (equalityOpen p u₁ u₂ h₁₂).ι = D.ι := T.homOfLE_ι inf_le_left
  have hr₂ : r₂ ≫ (equalityOpen p u₂ u₃ h₂₃).ι = D.ι := T.homOfLE_ι inf_le_right
  constructor
  · have he := congrArg (r₁ ≫ ·) (equalityOpen_eq p u₁ u₂ h₁₂)
    simpa only [← Category.assoc, hr₁] using he
  · have he := congrArg (r₂ ≫ ·) (equalityOpen_eq p u₂ u₃ h₂₃)
    simpa only [← Category.assoc, hr₂] using he

#print axioms triple_diagonal_sup_generic
#print axioms triple_diagonal_base_eq

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
