/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Opaque abstract combination of actual prescribed chart pullback and original
beta conjugation. No native pseudofunctor is unfolded and no budget is raised.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLinePullRestriction

set_option autoImplicit false
noncomputable section
universe u v u' v'
open CategoryTheory Opposite CategoryTheory.Bicategory
open CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract

/-- A global map's actual generic chart equation implies actual further beta conjugation. -/
theorem pullHom_of_conjugated_chart
    {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
    {X Xg A T H T' : C} (i : Xg ⟶ X) (q : Xg ⟶ A)
    {M : F.obj (.mk (op X))} {L : F.obj (.mk (op A))}
    (β : (F.map i.op.toLoc).toFunctor.obj M ≅ (F.map q.op.toLoc).toFunctor.obj L)
    (x y : T ⟶ X) (j : H ⟶ T) (a b : H ⟶ Xg)
    (hx : a ≫ i = j ≫ x) (hy : b ≫ i = j ≫ y) (hq : a ≫ q = b ≫ q)
    (E : (F.map x.op.toLoc).toFunctor.obj M ⟶ (F.map y.op.toLoc).toFunctor.obj M)
    (hE : (F.map j.op.toLoc).toFunctor.map E =
      pullHomMapComp'
        (pullHom β.hom a (j ≫ x) (a ≫ q) hx rfl ≫
          pullHom β.inv b (a ≫ q) (j ≫ y) hq.symm hy)
        x y (𝟙 H) j j (by simp) (by simp))
    (r : T' ⟶ H) (t : T' ⟶ T) (hrt : r ≫ j = t)
    (x' y' : T' ⟶ X) (hx' : t ≫ x = x') (hy' : t ≫ y = y') :
    pullHom E t x' y' hx' hy' =
      pullHom β.hom (r ≫ a) x' (r ≫ (a ≫ q))
        (by rw [Category.assoc, hx, ← Category.assoc, hrt, hx'])
        (by rw [Category.assoc]) ≫
      pullHom β.inv (r ≫ b) (r ≫ (a ≫ q)) y'
        (by rw [Category.assoc, ← hq])
        (by rw [Category.assoc, hy, ← Category.assoc, hrt, hy']) := by
  exact (pullHom_of_chart_map_comp x y j E _ hE r t hrt x' y' hx' hy').trans
    (pullHom_conjugatedComparisons_of_eq i q β a b (j ≫ x) (j ≫ y) (a ≫ q)
      hx hy rfl hq.symm r x' y' (r ≫ (a ≫ q))
      (by rw [← Category.assoc, hrt, hx'])
      (by rw [← Category.assoc, hrt, hy']) rfl)

#print axioms pullHom_of_conjugated_chart

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract
