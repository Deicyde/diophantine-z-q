-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.ProjectiveSpace.Empty), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Basic

/-!
# Projective space with no coordinates

The projective spectrum of a polynomial ring on an empty set of homogeneous
coordinates is empty.
-/

universe u v

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective space with no homogeneous coordinates is empty. -/
instance isEmpty_projectiveSpaceOverAffine (coordinates : Type v) (coefficients : Type (max u v))
    [CommRing coefficients] [IsEmpty coordinates] :
    IsEmpty (projectiveSpaceOverAffine coordinates coefficients) :=
  ⟨fun point ↦ by
    have covered : point ∈ ⨆ index : coordinates,
        basicOpen (MvPolynomial.homogeneousSubmodule coordinates coefficients)
          (MvPolynomial.X index) := by
      rw [iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule coordinates coefficients)
        (MvPolynomial.X : coordinates → MvPolynomial coordinates coefficients)
        (fun index ↦ ⟨1, MvPolynomial.isHomogeneous_X coefficients index⟩)
        (MvPolynomial.adjoin_range_X_eq_top coordinates coefficients)]
      trivial
    obtain ⟨index, _⟩ := TopologicalSpace.Opens.mem_iSup.mp covered
    exact isEmptyElim index⟩

end AlgebraicGeometry.Proj
