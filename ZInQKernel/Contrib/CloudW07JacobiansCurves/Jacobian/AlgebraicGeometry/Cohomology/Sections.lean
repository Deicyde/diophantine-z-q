-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Cohomology.Sections), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Basic
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.GlobalSection

/-!
# Structure-module morphisms and zeroth cohomology

Evaluation at one identifies morphisms from the structure module with global
sections, and hence with zeroth sheaf cohomology.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.H

variable {sourceScheme : Scheme.{u}}

/-- A structure-module morphism determines its actual zeroth cohomology class. -/
def unitHomAddEquiv (moduleSheaf : sourceScheme.Modules) :
    (unit sourceScheme ⟶ moduleSheaf) ≃+ moduleSheaf.H 0 :=
  (Modules.unitHomAddEquiv moduleSheaf).trans (zeroLinearEquiv moduleSheaf).symm.toAddEquiv

end AlgebraicGeometry.Scheme.Modules.H
