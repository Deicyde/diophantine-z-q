/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Ordinary-category hom equality transport, keeping native module category
dictionaries abstract until the final consumer. No scheme/line/cocycle or
ampleness hypothesis is introduced.
-/
import Mathlib.CategoryTheory.Iso

set_option autoImplicit false
universe u v
open CategoryTheory

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract

/-- Two actual isomorphisms with the SAME proved common hom are equal. -/
theorem iso_eq_of_common_hom {D : Type u} [Category.{v} D] {X Y : D}
    (a b : X ≅ Y) (f : X ⟶ Y) (ha : a.hom = f) (hb : b.hom = f) : a = b :=
  Iso.ext (ha.trans hb.symm)

/-- A proved normalization and a proved hom law compose without native rewrites. -/
theorem hom_eq_of_normalization {D : Type u} [Category.{v} D] {X Y : D}
    (a b c : X ⟶ Y) (hab : a = b) (hbc : b = c) : a = c :=
  hab.trans hbc

#print axioms iso_eq_of_common_hom
#print axioms hom_eq_of_normalization

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract
