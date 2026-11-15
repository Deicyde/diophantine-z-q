-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Curve.SeparatingFunction), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.FunctionFieldDifferentials
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.FunctionField
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.Kaehler.SeparatingElement

/-!
# Separating rational functions on smooth curves

For an integral smooth curve whose function field contains a transcendental
element, one can choose a transcendental rational function with nonzero
differential. Any intermediate ring containing it makes the function field
formally unramified.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory KaehlerDifferential

namespace AlgebraicGeometry.Scheme

/-- A smooth integral curve with a nonzero-dimensional local ring has a
transcendental rational function with nonzero differential over the ground field. -/
theorem exists_separating_functionField {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} [scheme.Over (Spec (.of baseField))] [IsIntegral scheme]
    [SmoothOfRelativeDimension 1 (scheme ↘ Spec (.of baseField))]
    (point : scheme) (positive_dimension : ringKrullDim (scheme.presheaf.stalk point) ≠ 0) :
    ∃ element : scheme.functionField,
      letI := (functionFieldRingHom baseField scheme).toAlgebra
      Transcendental baseField element ∧ D baseField scheme.functionField element ≠ 0 := by
  obtain ⟨element, transcendental⟩ :=
    exists_transcendental_functionField (baseField := baseField) point positive_dimension
  let := (functionFieldRingHom baseField scheme).toAlgebra
  have dimension : Module.finrank scheme.functionField Ω[scheme.functionField⁄baseField] = 1 :=
    finrank_kaehlerDifferential_functionField (scheme ↘ Spec (.of baseField)) 1
      (Scheme.ΓSpecIso (.of baseField)).symm.commRingCatIsoToRingEquiv rfl
  exact exists_transcendental_and_D_ne_zero dimension transcendental

/-- Every smooth proper integral curve has a transcendental rational function
with nonzero differential over its ground field. -/
theorem exists_separating_functionField_of_isProper {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} [scheme.Over (Spec (.of baseField))] [IsIntegral scheme]
    [SmoothOfRelativeDimension 1 (scheme ↘ Spec (.of baseField))]
    [IsProper (scheme ↘ Spec (.of baseField))] :
    ∃ element : scheme.functionField,
      letI := (functionFieldRingHom baseField scheme).toAlgebra
      Transcendental baseField element ∧ D baseField scheme.functionField element ≠ 0 := by
  have : Smooth (scheme ↘ Spec (.of baseField)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian scheme := LocallyOfFiniteType.isLocallyNoetherian
    (scheme ↘ Spec (.of baseField))
  have : CompactSpace scheme := QuasiCompact.compactSpace_of_compactSpace
    (scheme ↘ Spec (.of baseField))
  obtain ⟨point, -, closed⟩ := isClosed_univ.exists_closed_singleton
    (X := scheme) Set.univ_nonempty
  apply exists_separating_functionField (baseField := baseField) point
  rw [ringKrullDim_stalk_eq_one_of_isClosed (scheme ↘ Spec (.of baseField)) closed]
  exact one_ne_zero

end AlgebraicGeometry.Scheme
