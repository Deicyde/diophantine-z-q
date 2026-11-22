/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Data.Complex.Basic

/-!
# The category of schemes locally of finite type over the lifted complex field

The three declarations below are moved unchanged from `Oka/Analytification/Scheme.lean`
at source pin `9a9fc315498d58484ac1abc9668548212eb7c1ff`. That module imports this
one and no longer redeclares them. These are the authoritative original objects,
not substitute definitions or aliases to a different projective-space model.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

/-- `Spec ℂ` as a scheme in universe `u`: the spectrum of `ULift.{u} ℂ`. -/
noncomputable abbrev Specℂ : Scheme.{u} := Spec (CommRingCat.of (ULift.{u} ℂ))

/-- The property of a scheme over `ℂ` of being locally of finite type. -/
def locallyOfFiniteTypeℂ : ObjectProperty (Over (Specℂ.{u})) :=
  fun X ↦ LocallyOfFiniteType X.hom

/-- **The category of schemes locally of finite type over `ℂ`**, as a full subcategory of the
schemes over `Spec ℂ`. -/
abbrev SchemeLFTℂ : Type (u + 1) := locallyOfFiniteTypeℂ.FullSubcategory

end ComplexAnalytic
