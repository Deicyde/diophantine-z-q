/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Canonical equality-map composition for an ordinary object family, abstract
from schemes, functors, native coefficient dictionaries and chosen line isos.
-/
import Mathlib.CategoryTheory.EqToHom

set_option autoImplicit false
universe u v w
open CategoryTheory

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract

/-- The third equality comparison is the LITERAL supplied equality, not a
new desired cocycle premise. Proof irrelevance identifies its equality proof. -/
theorem familyEquality_composition
    {D : Type u} [Category.{v} D] {I : Type w} (P : I → D)
    (i j k : I) (hij : i = j) (hjk : j = k) (hik : i = k)
    (a : P i ⟶ P j) (b : P j ⟶ P k) (c : P i ⟶ P k)
    (ha : a = eqToHom (congrArg P hij))
    (hb : b = eqToHom (congrArg P hjk))
    (hc : c = eqToHom (congrArg P hik)) : a ≫ b = c := by
  rw [ha, hb, hc]
  exact eqToHom_trans (congrArg P hij) (congrArg P hjk)

#print axioms familyEquality_composition

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract
