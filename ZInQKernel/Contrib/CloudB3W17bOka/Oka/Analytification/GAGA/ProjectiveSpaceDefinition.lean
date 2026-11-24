/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AlgebraicGeometry.ProjectiveSpace.Basic
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.SchemeLFTComplex

/-!
# The genuine algebraic projective-space object over the lifted complex field

Moved unchanged, after the explicit collision-safe type/API rename, from
`Oka/Analytification/GAGA/ProjectiveSpace.lean` at source pin
`9a9fc315498d58484ac1abc9668548212eb7c1ff`. The original module imports this
one and no longer redeclares these constants. This remains Oka's actual Proj
construction, not W07's different relative projective space under an alias.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

/-- **Projective `n`-space over `ℂ`**, `Proj ℂ[X₀, …, Xₙ]`, as a scheme locally of finite type. -/
noncomputable def projectiveSpace (n : ℕ) : SchemeLFTℂ.{u} :=
  ⟨Over.mk (CloudB3W17bOkaProjectiveSpace.toSpec n (ULift.{u} ℂ)),
    show LocallyOfFiniteType (CloudB3W17bOkaProjectiveSpace.toSpec n _) from inferInstance⟩

@[simp]
lemma projectiveSpace_obj_left (n : ℕ) :
    (projectiveSpace.{u} n).obj.left = (AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace (n) (ULift.{u} ℂ)) :=
  rfl

@[simp]
lemma projectiveSpace_obj_hom (n : ℕ) :
    (projectiveSpace.{u} n).obj.hom = CloudB3W17bOkaProjectiveSpace.toSpec n (ULift.{u} ℂ) :=
  rfl

end ComplexAnalytic
