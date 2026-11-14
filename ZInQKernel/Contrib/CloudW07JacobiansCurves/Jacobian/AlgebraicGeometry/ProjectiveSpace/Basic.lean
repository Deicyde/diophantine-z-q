-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.ProjectiveSpace.Basic), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Projective space over an affine base

The projective spectrum of a polynomial ring, with its total-degree grading,
is projective space over the spectrum of the coefficient ring. Its structure
morphism is proper when the set of homogeneous coordinates is finite.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates : Type v) (coefficients : Type (max u v)) [CommRing coefficients]

/-- Projective space with the given homogeneous coordinates over an affine base. -/
abbrev projectiveSpaceOverAffine : Scheme.{max u v} :=
  Proj (MvPolynomial.homogeneousSubmodule coordinates coefficients)

/-- The structure morphism induced by the inclusion of constants in degree zero. -/
def projectiveSpaceOverAffineToSpec :
    projectiveSpaceOverAffine coordinates coefficients ⟶ Spec (.of coefficients) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule coordinates coefficients) ≫
    Spec.map (CommRingCat.ofHom
      (MvPolynomial.homogeneousSubmoduleZeroEquiv coordinates coefficients).toRingHom)

/-- Projective space with finitely many homogeneous coordinates is proper over its base. -/
instance instIsProperProjectiveSpaceOverAffineToSpec [Finite coordinates] :
    IsProper (projectiveSpaceOverAffineToSpec coordinates coefficients) := by
  rw [projectiveSpaceOverAffineToSpec]
  haveI : IsProper (toSpecZero (MvPolynomial.homogeneousSubmodule coordinates coefficients)) :=
    inferInstance
  haveI : IsIso (CommRingCat.ofHom
      (MvPolynomial.homogeneousSubmoduleZeroEquiv coordinates coefficients).toRingHom) := by
    change IsIso
      (MvPolynomial.homogeneousSubmoduleZeroEquiv coordinates coefficients).toCommRingCatIso.hom
    infer_instance
  infer_instance

end AlgebraicGeometry.Proj
