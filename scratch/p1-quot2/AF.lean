import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.FiniteSet

/-! p1-quot2: EGA II 4.5.4 (Liu Prop. 3.3.36 (b)) over an affine base: a finite set of points of a closed
subscheme of `ℙ(ι; Spec R)` lies in an affine open. The proof is the vendored field case
(`AlgebraicGeometry.exists_isAffineOpen_superset_of_isClosedImmersion`), which uses only that the base is
affine. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace P1Quot2

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_isAffineOpen_superset_of_isClosedImmersion_spec
    {R : CommRingCat.{u}} {X : Scheme.{u}}
    {ι : Type u} (i : X ⟶ ℙ(ι; Spec R))
    [IsClosedImmersion i] (s : Set X) (hs : s.Finite) :
    ∃ W : X.Opens, IsAffineOpen W ∧ s ⊆ W := by
  classical
  let j := i ≫ ProjectiveSpace.toIntegralModel ι (Spec R)
  obtain ⟨d, hd, f, hf, havoid⟩ :=
    ProjectiveSpectrum.exists_homogeneous_notMem_of_finset
      (grading := MvPolynomial.homogeneousSubmodule ι (ULift.{u} ℤ))
      (hs.image j.base).toFinset
  have hA := Proj.isAffineOpen_basicOpen
    (MvPolynomial.homogeneousSubmodule ι (ULift.{u} ℤ)) f hf hd
  haveI : IsAffineHom (ProjectiveSpace.toIntegralModel ι (Spec R)) := by
    haveI : IsAffineHom (terminal.from (Spec R)) := isAffineHom_of_isAffine _
    exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  refine ⟨j ⁻¹ᵁ Proj.basicOpen _ f, hA.preimage j, fun x hx ↦ ?_⟩
  exact havoid (j.base x) (by simpa using ⟨x, hx, rfl⟩)

end P1Quot2
