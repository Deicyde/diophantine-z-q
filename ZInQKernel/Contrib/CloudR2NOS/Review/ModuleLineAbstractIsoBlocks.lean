/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Ordinary-category regrouping of nine isomorphisms into literal 5/4 blocks.
No native scheme/functor, line cocycle or ampleness hypothesis is present.
-/
import Mathlib.CategoryTheory.Iso

set_option autoImplicit false
universe u v
open CategoryTheory

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract

theorem iso_regroup_nine {D : Type u} [Category.{v} D]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : D}
    (a₁ : X₀ ≅ X₁) (a₂ : X₁ ≅ X₂) (a₃ : X₂ ≅ X₃)
    (a₄ : X₃ ≅ X₄) (a₅ : X₄ ≅ X₅) (a₆ : X₅ ≅ X₆)
    (a₇ : X₆ ≅ X₇) (a₈ : X₇ ≅ X₈) (a₉ : X₈ ≅ X₉) :
    a₁ ≪≫ a₂ ≪≫ a₃ ≪≫ a₄ ≪≫ a₅ ≪≫ a₆ ≪≫ a₇ ≪≫ a₈ ≪≫ a₉ =
      (a₁ ≪≫ a₂ ≪≫ a₃ ≪≫ a₄ ≪≫ a₅) ≪≫ (a₆ ≪≫ a₇ ≪≫ a₈ ≪≫ a₉) := by
  simp only [Iso.trans_assoc]

/-- Two actual blocks compose by their proved homs in ONE abstract category. -/
theorem iso_blocks_hom {D : Type u} [Category.{v} D] {X Y Z : D}
    (a : X ≅ Y) (b : Y ≅ Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (ha : a.hom = f) (hb : b.hom = g) : (a ≪≫ b).hom = f ≫ g :=
  (Iso.trans_hom a b).trans (congrArg₂ (fun p q => p ≫ q) ha hb)

#print axioms iso_regroup_nine
#print axioms iso_blocks_hom

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract
