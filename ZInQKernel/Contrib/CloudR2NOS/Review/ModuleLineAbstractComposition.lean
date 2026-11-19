/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Ordinary-category equality composition. Native category dictionaries, maps,
and coefficient objects are instantiated once by the consumer. No Scheme,
line-bundle, descent, ampleness, or NOS hypothesis is part of this primitive.
-/
import Mathlib.CategoryTheory.Category.Basic

set_option autoImplicit false
universe u v
open CategoryTheory

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract

/-- Three proved comparisons and their proved composition give the desired
composition, without rewriting native object dictionaries at the boundary. -/
theorem composition_of_comparisons
    {D : Type u} [Category.{v} D] {X Y Z : D}
    (a a₀ : X ⟶ Y) (b b₀ : Y ⟶ Z) (c c₀ : X ⟶ Z)
    (ha : a = a₀) (hb : b = b₀) (hc : c = c₀) (hcomp : a₀ ≫ b₀ = c₀) :
    a ≫ b = c :=
  (congrArg₂ (fun f g => f ≫ g) ha hb).trans (hcomp.trans hc.symm)

#print axioms composition_of_comparisons

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract
