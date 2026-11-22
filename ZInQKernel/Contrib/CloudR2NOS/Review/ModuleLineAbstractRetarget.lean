/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Opaque abstract pseudofunctor retargeting of ACTUAL equal generic lifts and
ACTUAL equal original-variety coordinates. No cocycle/line extension/VA/NOS
conclusion is an input. Used to keep native kernel reduction bounded.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLinePullHom

set_option autoImplicit false
noncomputable section
universe u v u' v'
open CategoryTheory Opposite CategoryTheory.Bicategory
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract

/-- Equal actual lifts/coordinates give the SAME conjugated coefficient map. -/
theorem conjugatedComparisons_retarget
    {C : Type u} [Category.{v} C]
    {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
    {X Xg A T : C} (i : Xg ⟶ X) (q : Xg ⟶ A)
    {M : F.obj (.mk (op X))} {L : F.obj (.mk (op A))}
    (β : (F.map i.op.toLoc).toFunctor.obj M ≅ (F.map q.op.toLoc).toFunctor.obj L)
    (r₁ r₂ a b : T ⟶ Xg) (x y : T ⟶ X) (z z' : T ⟶ A)
    (h₁x : r₁ ≫ i = x) (h₂y : r₂ ≫ i = y)
    (h₁z : r₁ ≫ q = z) (h₂z : r₂ ≫ q = z)
    (hax : a ≫ i = x) (hby : b ≫ i = y)
    (haz : a ≫ q = z') (hbz : b ≫ q = z')
    (hra : r₁ = a) (hrb : r₂ = b) (hzz : z = z') :
    pullHom (F := F) β.hom r₁ x z h₁x h₁z ≫
        pullHom (F := F) β.inv r₂ z y h₂z h₂y =
      pullHom (F := F) β.hom a x z' hax haz ≫
        pullHom (F := F) β.inv b z' y hbz hby := by
  subst a b z'
  rfl

#print axioms conjugatedComparisons_retarget

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract
