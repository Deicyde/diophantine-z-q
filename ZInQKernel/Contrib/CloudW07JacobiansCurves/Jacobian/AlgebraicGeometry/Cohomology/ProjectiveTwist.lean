-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Cohomology.ProjectiveTwist), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.ProjectiveSpace
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist

/-!
# Cohomological dimension for twisting sheaves

The twisting sheaves on projective `d`-space have no cohomology above degree `d`.
This is a vanishing statement for the actual sheaf cohomology of `𝒪(m)` over any
commutative coefficient ring.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates : Type v) (coefficients : Type (max u v)) [CommRing coefficients]

/-- Twisting sheaves on projective `d`-space have no cohomology above degree `d`. -/
theorem subsingleton_H_twist_homogeneousSubmodule_of_lt [Finite coordinates]
    {dimension : ℕ} (coordinateCount : Nat.card coordinates = dimension + 1)
    (twistDegree : ℤ) {degree : ℕ} (degreeBound : dimension < degree) :
    Subsingleton ((twist (MvPolynomial.homogeneousSubmodule coordinates coefficients)
      twistDegree).H degree) := by
  letI : SheafOfModules.IsQuasicoherent
      (R := (projectiveSpaceOverAffine coordinates coefficients).ringCatSheaf)
      (twist (MvPolynomial.homogeneousSubmodule coordinates coefficients) twistDegree) :=
    SheafOfModules.IsInvertible.isQuasicoherent.{max u v, max u v, max u v}
      (isInvertible_twist_homogeneousSubmodule coordinates coefficients twistDegree)
  exact subsingleton_H_projectiveSpaceOverAffine_of_lt coordinates coefficients coordinateCount
    (twist (MvPolynomial.homogeneousSubmodule coordinates coefficients) twistDegree) degreeBound

end AlgebraicGeometry.Proj
