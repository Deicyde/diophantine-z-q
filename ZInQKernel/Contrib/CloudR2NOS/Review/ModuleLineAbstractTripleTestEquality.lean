/-
NEW H5 edition (lost original), authored from importer usage; helper of lead 21826d9b
-/
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v u' v'
open CategoryTheory Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract

variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

/-- A proved composition law for three test morphisms gives the pulled-back hom law. -/
theorem triple_tests_equality {X₁ X₂ X₃ Y Z : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {M₃ : F.obj (.mk (op X₃))}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (f₃ : Y ⟶ X₃)
    (φ₁₂ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (φ₂₃ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (φ₁₃ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (t : Z ⟶ Y) (x₁ : Z ⟶ X₁) (x₂ : Z ⟶ X₂) (x₃ : Z ⟶ X₃)
    (h₁ : t ≫ f₁ = x₁) (h₂ : t ≫ f₂ = x₂) (h₃ : t ≫ f₃ = x₃)
    (a₁₂ : (F.map x₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map x₂.op.toLoc).toFunctor.obj M₂)
    (a₂₃ : (F.map x₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map x₃.op.toLoc).toFunctor.obj M₃)
    (a₁₃ : (F.map x₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map x₃.op.toLoc).toFunctor.obj M₃)
    (ha₁₂ : pullHom φ₁₂ t x₁ x₂ h₁ h₂ = a₁₂)
    (ha₂₃ : pullHom φ₂₃ t x₂ x₃ h₂ h₃ = a₂₃)
    (ha₁₃ : pullHom φ₁₃ t x₁ x₃ h₁ h₃ = a₁₃)
    (hc : a₁₂ ≫ a₂₃ = a₁₃) :
    pullHom (φ₁₂ ≫ φ₂₃) t x₁ x₃ h₁ h₃ = pullHom φ₁₃ t x₁ x₃ h₁ h₃ := by
  have hp : pullHom (φ₁₂ ≫ φ₂₃) t x₁ x₃ h₁ h₃ =
      pullHom φ₁₂ t x₁ x₂ h₁ h₂ ≫ pullHom φ₂₃ t x₂ x₃ h₂ h₃ := by
    simp only [pullHom, Functor.map_comp, Category.assoc,
      Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  exact hp.trans ((congrArg₂ (fun f g => f ≫ g) ha₁₂ ha₂₃).trans (hc.trans ha₁₃.symm))

/-- Equal coherent pullbacks have equal underlying functor maps. -/
theorem map_eq_of_pullHom_eq {X₁ X₂ Y Z : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (φ ψ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (t : Z ⟶ Y) (x₁ : Z ⟶ X₁) (x₂ : Z ⟶ X₂)
    (h₁ : t ≫ f₁ = x₁) (h₂ : t ≫ f₂ = x₂)
    (h : pullHom φ t x₁ x₂ h₁ h₂ = pullHom ψ t x₁ x₂ h₁ h₂) :
    (F.map t.op.toLoc).toFunctor.map φ = (F.map t.op.toLoc).toFunctor.map ψ := by
  rw [map_eq_pullHom φ t x₁ x₂ h₁ h₂,
    map_eq_pullHom ψ t x₁ x₂ h₁ h₂, h]

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract
