-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.ProjectiveSpace.FiniteSet), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Relative
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpectrum.FiniteSet

/-!
# Affine neighbourhoods of finite sets in projective schemes

Homogeneous prime avoidance in the integral projective model gives a basic open
containing any prescribed finite set. Pulling it back along a closed projective
embedding gives an affine neighbourhood in the embedded scheme.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite set in a closed subscheme of projective space over a field lies
in a common affine open. -/
theorem exists_isAffineOpen_superset_of_isClosedImmersion
    {baseField : Type u} [Field baseField] {sourceScheme : Scheme.{u}}
    {coordinates : Type u} (embedding : sourceScheme ⟶ ℙ(coordinates; Spec (.of baseField)))
    [IsClosedImmersion embedding] (points : Set sourceScheme) (finitePoints : points.Finite) :
    ∃ openSubset : sourceScheme.Opens, IsAffineOpen openSubset ∧ points ⊆ openSubset := by
  classical
  let integralProjection := embedding ≫
    ProjectiveSpace.toIntegralModel coordinates (Spec (.of baseField))
  obtain ⟨degree, positiveDegree, homogeneousElement, homogeneous, avoidsPoints⟩ :=
    ProjectiveSpectrum.exists_homogeneous_notMem_of_finset
      (grading := MvPolynomial.homogeneousSubmodule coordinates (ULift.{u} ℤ))
      (finitePoints.image integralProjection.base).toFinset
  have affineBasicOpen := Proj.isAffineOpen_basicOpen
    (MvPolynomial.homogeneousSubmodule coordinates (ULift.{u} ℤ))
    homogeneousElement homogeneous positiveDegree
  haveI : IsAffineHom (ProjectiveSpace.toIntegralModel coordinates
      (Spec (.of baseField))) := by
    haveI : IsAffineHom (terminal.from (Spec (.of baseField))) := isAffineHom_of_isAffine _
    exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  refine ⟨integralProjection ⁻¹ᵁ Proj.basicOpen _ homogeneousElement,
    affineBasicOpen.preimage integralProjection, fun point membership ↦ ?_⟩
  exact avoidsPoints (integralProjection.base point) (by simpa using ⟨point, membership, rfl⟩)

end AlgebraicGeometry
