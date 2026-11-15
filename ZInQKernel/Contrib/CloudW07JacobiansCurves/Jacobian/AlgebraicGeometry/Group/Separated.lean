-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Group.Separated), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Group schemes over a field are separated

The unit section is a closed immersion. The shear automorphism carries its
base-changed slice to the diagonal, so the diagonal is a closed immersion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Every group scheme over a field is separated over that field. -/
instance GrpObj.isSeparated_hom {baseField : Type u} [Field baseField]
    (group : Over (Spec (.of baseField))) [GrpObj group] : IsSeparated group.hom := by
  have unitClosed : IsClosedImmersion η[group].left :=
    isClosedImmersion_of_comp_eq_id group.hom _ (Over.w η[group])
  have diagonal_eq : lift (𝟙 group) (𝟙 group) =
      ((ρ_ group).inv ≫ group ◁ η[group]) ≫
        (CategoryTheory.GrpObj.shearIso group).hom := by
    ext <;> simp [MonObj.comp_mul, ← Hom.one_def]
  letI : IsClosedImmersion (group ◁ η[group]).left := by
    rw [Over.whiskerLeft_left]
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (MorphismProperty.id_mem _ _) unitClosed (by simp) (by simp)
  refine ⟨?_⟩
  have diagonal : Limits.pullback.diagonal group.hom =
      (lift (𝟙 group) (𝟙 group)).left := by
    ext <;> simp
  rw [diagonal, diagonal_eq, Over.comp_left, Over.comp_left]
  infer_instance

end AlgebraicGeometry
