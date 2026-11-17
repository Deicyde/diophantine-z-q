-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.ProjectiveLine.Basic), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The projective line

The projective line over a field is the projective spectrum of the polynomial
ring in two variables, graded by total degree. The coefficient inclusion gives
its structure morphism to the spectrum of the field.
-/
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective line Proj(k[X₀,X₁]) with the total-degree grading. -/
def projectiveLine (k : Type u) [Field k] : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

/-- The structural map of Proj(k[X₀,X₁]) to Spec k, using the degree-zero
coefficient inclusion in the graded polynomial ring. -/
def projectiveLineToSpec (k : Type u) [Field k] : projectiveLine k ⟶ Spec (.of k) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin 2) k 0)))

/-- The projective line bundled as a scheme over the ground field. -/
def projectiveLineOver (k : Type u) [Field k] : Over (Spec (.of k)) :=
  Over.mk (projectiveLineToSpec k)

end AlgebraicGeometry
