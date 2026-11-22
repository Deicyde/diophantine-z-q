/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Opaque abstract local test-composition bridge. The supplied local comparison
equalities are consumed from actual already-proved diagonal/generic tests,
not introduced as final NOS/global line-cocycle premises.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineAbstractTestPull

set_option autoImplicit false
noncomputable section
universe u v u' v'
open CategoryTheory Opposite CategoryTheory.Bicategory
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract

/-- Actual local triple comparisons certify equality of coherent composite tests. -/
theorem triple_tests_equality
    {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
    {X Y T : C} {M : F.obj (.mk (op X))}
    (f₁ f₂ f₃ : Y ⟶ X)
    (φ₁₂ : (F.map f₁.op.toLoc).toFunctor.obj M ⟶ (F.map f₂.op.toLoc).toFunctor.obj M)
    (φ₂₃ : (F.map f₂.op.toLoc).toFunctor.obj M ⟶ (F.map f₃.op.toLoc).toFunctor.obj M)
    (φ₁₃ : (F.map f₁.op.toLoc).toFunctor.obj M ⟶ (F.map f₃.op.toLoc).toFunctor.obj M)
    (t : T ⟶ Y) (x y z : T ⟶ X)
    (hx : t ≫ f₁ = x) (hy : t ≫ f₂ = y) (hz : t ≫ f₃ = z)
    (a : (F.map x.op.toLoc).toFunctor.obj M ⟶ (F.map y.op.toLoc).toFunctor.obj M)
    (b : (F.map y.op.toLoc).toFunctor.obj M ⟶ (F.map z.op.toLoc).toFunctor.obj M)
    (c : (F.map x.op.toLoc).toFunctor.obj M ⟶ (F.map z.op.toLoc).toFunctor.obj M)
    (ha : pullHom (F := F) φ₁₂ t x y hx hy = a)
    (hb : pullHom (F := F) φ₂₃ t y z hy hz = b)
    (hc : pullHom (F := F) φ₁₃ t x z hx hz = c) (hab : a ≫ b = c) :
    pullHom (F := F) (φ₁₂ ≫ φ₂₃) t x z hx hz =
      pullHom (F := F) φ₁₃ t x z hx hz :=
  (pullHom_comp φ₁₂ φ₂₃ t x y z hx hy hz).trans
    ((congrArg₂ (fun f g => f ≫ g) ha hb).trans (hab.trans hc.symm))

#print axioms triple_tests_equality

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract
