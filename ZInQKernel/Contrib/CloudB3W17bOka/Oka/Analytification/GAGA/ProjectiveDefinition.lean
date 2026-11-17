/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.GAGA.ProjectiveSpaceDefinition
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual projectivity over the lifted complex field

The original declaration below is moved unchanged from
`Oka/Analytification/GAGA/ProjectiveGAGA.lean` at source pin
`9a9fc315498d58484ac1abc9668548212eb7c1ff`. That module imports this one and
no longer declares it. It uses the genuine original Oka projective-space object,
with its explicit collision-safe name; no substitute predicate or extra premise
has been introduced for a bridge author.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

/-- A scheme locally of finite type over `ℂ` is **projective** if it admits a closed immersion
over `ℂ` into some projective space `ℙⁿ_ℂ`. -/
def IsProjectiveℂ (X : SchemeLFTℂ.{u}) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ projectiveSpace.{u} n), IsClosedImmersion i.hom.left

end ComplexAnalytic
