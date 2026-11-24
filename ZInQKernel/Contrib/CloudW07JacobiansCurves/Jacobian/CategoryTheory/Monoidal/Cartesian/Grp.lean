-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.CategoryTheory.Monoidal.Cartesian.Grp), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Shear isomorphisms for group objects

The shear automorphism of the square of a group object sends `(g, h)` to
`(g, g * h)`. Its inverse sends `(g, h)` to `(g, g⁻¹ * h)`.
-/

universe v u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace CategoryTheory.GrpObj

variable {category : Type u} [Category.{v} category] [CartesianMonoidalCategory category]

/-- The shear automorphism `(g, h) ↦ (g, g * h)` of the square of a group object. -/
@[simps]
noncomputable def shearIso (group : category) [GrpObj group] : group ⊗ group ≅ group ⊗ group where
  hom := lift (fst group group) (fst group group * snd group group)
  inv := lift (fst group group) ((fst group group)⁻¹ * snd group group)
  hom_inv_id := by
    ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv]
  inv_hom_id := by
    ext <;> simp [MonObj.comp_mul]

end CategoryTheory.GrpObj
