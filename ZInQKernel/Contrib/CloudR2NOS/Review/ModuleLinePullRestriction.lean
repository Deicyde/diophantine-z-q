/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Opaque abstract restriction of the actual global line map to a prescribed
chart. All comparison morphisms are the original pseudofunctor comparisons.
The local map equation is an explicit INTERMEDIATE output of the proved
Zariski gluing, not a new hypothesis of NOS, extension or effectiveness.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLinePullHom

set_option autoImplicit false
noncomputable section
universe u v u' v'

open CategoryTheory Opposite CategoryTheory.Bicategory
open CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract

variable {C : Type u} [Category.{v} C]
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- A literal prescribed chart equation recovers the actual direct pullback. -/
theorem pullHom_of_chart_map
    {X₁ X₂ T U : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (x : T ⟶ X₁) (y : T ⟶ X₂) (j : U ⟶ T)
    (E : (F.map x.op.toLoc).toFunctor.obj M₁ ⟶ (F.map y.op.toLoc).toFunctor.obj M₂)
    (d : (F.map (j ≫ x).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (j ≫ y).op.toLoc).toFunctor.obj M₂)
    (he : (F.map j.op.toLoc).toFunctor.map E =
      pullHomMapComp' d x y (𝟙 U) j j (by simp) (by simp)) :
    pullHom E j (j ≫ x) (j ≫ y) rfl rfl = d := by
  let a := (F.mapComp' x.op.toLoc j.op.toLoc (j ≫ x).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app M₁
  let b := (F.mapComp' y.op.toLoc j.op.toLoc (j ≫ y).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app M₂
  have h : a ≫ pullHom E j (j ≫ x) (j ≫ y) rfl rfl ≫ b = a ≫ d ≫ b := by
    erw [map_eq_pullHom E j (j ≫ x) (j ≫ y) rfl rfl] at he
    dsimp only [pullHomMapComp'] at he
    rw [pullHom_id] at he
    exact he
  apply (cancel_epi a).mp
  apply (cancel_mono b).mp
  simpa only [Category.assoc] using h

/-- Further pullback of the actual chart equation, retaining explicit endpoints. -/
theorem pullHom_of_chart_map_comp
    {X₁ X₂ T U T' : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (x : T ⟶ X₁) (y : T ⟶ X₂) (j : U ⟶ T)
    (E : (F.map x.op.toLoc).toFunctor.obj M₁ ⟶ (F.map y.op.toLoc).toFunctor.obj M₂)
    (d : (F.map (j ≫ x).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (j ≫ y).op.toLoc).toFunctor.obj M₂)
    (he : (F.map j.op.toLoc).toFunctor.map E =
      pullHomMapComp' d x y (𝟙 U) j j (by simp) (by simp))
    (a : T' ⟶ U) (t : T' ⟶ T) (hat : a ≫ j = t)
    (x' : T' ⟶ X₁) (y' : T' ⟶ X₂)
    (hx : t ≫ x = x') (hy : t ≫ y = y') :
    pullHom E t x' y' hx hy =
      pullHom d a x' y'
        (by rw [← Category.assoc, hat, hx]) (by rw [← Category.assoc, hat, hy]) := by
  have h := congrArg
    (fun f => pullHom f a x' y'
      (by rw [← Category.assoc, hat, hx]) (by rw [← Category.assoc, hat, hy]))
    (pullHom_of_chart_map x y j E d he)
  rw [pullHom_pullHom] at h
  simpa only [hat] using h

#print axioms pullHom_of_chart_map
#print axioms pullHom_of_chart_map_comp

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract
