-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Morphisms.FinitePresentation), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.FinitePresentation

/-!
# Cancellation for locally finitely presented morphisms

If a composite is locally of finite presentation and its second factor is
locally of finite type, its first factor is locally of finite presentation.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Cancel a locally finite type second factor from local finite presentation. -/
theorem LocallyOfFinitePresentation.of_comp {source middle target : Scheme.{u}}
    (firstMap : source ⟶ middle) (secondMap : middle ⟶ target)
    [LocallyOfFinitePresentation (firstMap ≫ secondMap)] [LocallyOfFiniteType secondMap] :
    LocallyOfFinitePresentation firstMap :=
  HasRingHomProperty.of_comp_of (P' := @LocallyOfFiniteType)
    (fun _ _ finiteType finitePresentation ↦
      finitePresentation.of_comp_finiteType _ finiteType) ‹_› ‹_›

end AlgebraicGeometry
