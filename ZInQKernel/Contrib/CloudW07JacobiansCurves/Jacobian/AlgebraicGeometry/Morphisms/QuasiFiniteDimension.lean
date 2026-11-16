-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Morphisms.QuasiFiniteDimension), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Topology.KrullDimension.Maps
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# Dimension under quasi-finite surjections

A universally closed quasi-finite surjection preserves topological dimension.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Universally closed quasi-finite surjections preserve dimension. -/
theorem Scheme.Hom.topologicalKrullDim_eq_of_surjective (f : X ⟶ Y) [UniversallyClosed f]
    [LocallyQuasiFinite f] [Surjective f] : topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm
    (topologicalKrullDim_le_of_continuous f.continuous fun _ _ ↦ f.eq_of_specializes_of_apply_eq)
    (topologicalKrullDim_le_of_specializingMap f.isClosedMap.specializingMap f.surjective)

end AlgebraicGeometry
