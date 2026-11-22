/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Abstract pullHom restriction/ordinary functor-map equality bridge. This does
not assume a desired global line cocycle. It lets native open-cover equality
consume explicitly proved tests while keeping pseudofunctor fields opaque.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLinePullHom

set_option autoImplicit false
noncomputable section
universe u v u' v'
open CategoryTheory Opposite CategoryTheory.Bicategory
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract

/-- Equality of the coherent direct tests gives literal functor-map equality. -/
theorem map_eq_of_pullHom_eq
    {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
    {X₁ X₂ Y T : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (a b : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (t : T ⟶ Y) (x : T ⟶ X₁) (y : T ⟶ X₂)
    (hx : t ≫ f₁ = x) (hy : t ≫ f₂ = y)
    (h : pullHom (F := F) a t x y hx hy = pullHom (F := F) b t x y hx hy) :
    (F.map t.op.toLoc).toFunctor.map a = (F.map t.op.toLoc).toFunctor.map b := by
  rw [map_eq_pullHom a t x y hx hy, map_eq_pullHom b t x y hx hy, h]

/-- Further tests of an actual pulled comparison use the literal composite test. -/
theorem test_pullHom
    {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
    {X Y Z T : C} {M : F.obj (.mk (op X))}
    (f₁ f₂ : Y ⟶ X)
    (ψ : (F.map f₁.op.toLoc).toFunctor.obj M ⟶ (F.map f₂.op.toLoc).toFunctor.obj M)
    (c : Z ⟶ Y) (a b : Z ⟶ X) (hc₁ : c ≫ f₁ = a) (hc₂ : c ≫ f₂ = b)
    (t : T ⟶ Z) (x y : T ⟶ X) (hx : t ≫ a = x) (hy : t ≫ b = y) :
    pullHom (F := F) (pullHom (F := F) ψ c a b hc₁ hc₂) t x y hx hy =
      pullHom (F := F) ψ (t ≫ c) x y
        (by rw [Category.assoc, hc₁, hx]) (by rw [Category.assoc, hc₂, hy]) :=
  pullHom_pullHom ψ c a b t x y hc₁ hc₂ hx hy

#print axioms map_eq_of_pullHom_eq
#print axioms test_pullHom

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract
