/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

New generic PSEUDOFUNCTOR cancellation/naturality lemma, kept opaque before
specialization to native Scheme.Modules. It changes no kernel budgets, maps,
toolchain or source definition. Abstracting over F prevents kernel reduction
of the full Scheme.Modules pseudofunctor and isomorphism proof fields.
-/
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Sites.Descent.PullHom

set_option autoImplicit false
noncomputable section
universe u v u' v'

open CategoryTheory Opposite CategoryTheory.Bicategory
open CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

/-- Actual conjugated pullbacks commute with actual further base change, for
ANY pseudofunctor. No line/NOS/model assumption or budget escalation. -/
theorem pullHom_conjugatedComparisons
    {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
    {X Xg A T T' : C} (i : Xg ⟶ X) (q : Xg ⟶ A)
    {M : F.obj (.mk (op X))} {L : F.obj (.mk (op A))}
    (β : (F.map i.op.toLoc).toFunctor.obj M ≅ (F.map q.op.toLoc).toFunctor.obj L)
    (a b : T ⟶ Xg) (x y : T ⟶ X) (z : T ⟶ A)
    (hx : a ≫ i = x) (hy : b ≫ i = y) (ha : a ≫ q = z) (hb : b ≫ q = z)
    (t : T' ⟶ T) :
    pullHom (pullHom β.hom a x z hx ha ≫ pullHom β.inv b z y hb hy)
        t (t ≫ x) (t ≫ y) rfl rfl =
      pullHom β.hom (t ≫ a) (t ≫ x) (t ≫ z)
        (by rw [Category.assoc, hx]) (by rw [Category.assoc, ha]) ≫
      pullHom β.inv (t ≫ b) (t ≫ z) (t ≫ y)
        (by rw [Category.assoc, hb]) (by rw [Category.assoc, hy]) := by
  rw [pullHom_comp _ _ t (t ≫ x) (t ≫ z) (t ≫ y) rfl rfl rfl]
  rw [pullHom_pullHom, pullHom_pullHom]

#print axioms pullHom_conjugatedComparisons

/-- Explicit composite maps avoid simplifying dependent Scheme.Modules
objects when applying the opaque abstract naturality theorem. -/
theorem pullHom_conjugatedComparisons_of_eq
    {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
    {X Xg A T T' : C} (i : Xg ⟶ X) (q : Xg ⟶ A)
    {M : F.obj (.mk (op X))} {L : F.obj (.mk (op A))}
    (β : (F.map i.op.toLoc).toFunctor.obj M ≅ (F.map q.op.toLoc).toFunctor.obj L)
    (a b : T ⟶ Xg) (x y : T ⟶ X) (z : T ⟶ A)
    (hx : a ≫ i = x) (hy : b ≫ i = y) (ha : a ≫ q = z) (hb : b ≫ q = z)
    (t : T' ⟶ T) (x' y' : T' ⟶ X) (z' : T' ⟶ A)
    (htx : t ≫ x = x') (hty : t ≫ y = y') (htz : t ≫ z = z') :
    pullHom (pullHom β.hom a x z hx ha ≫ pullHom β.inv b z y hb hy)
        t x' y' htx hty =
      pullHom β.hom (t ≫ a) x' z'
        (by rw [Category.assoc, hx, htx]) (by rw [Category.assoc, ha, htz]) ≫
      pullHom β.inv (t ≫ b) z' y'
        (by rw [Category.assoc, hb, htz]) (by rw [Category.assoc, hy, hty]) := by
  subst x' y' z'
  exact pullHom_conjugatedComparisons i q β a b x y z hx hy ha hb t

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
