-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Curve.FiniteTraceSections), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.TraceSections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveLine.BasicOpens

/-!
# Differential traces for finite flat maps to the projective line

Over polynomial basic opens in the target, the algebra of sections of a finite
flat curve map is finite free. This supplies the trace construction with its
actual finite-free module instances.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

open ProjectiveLine Polynomial

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  (morphism : source ⟶ projectiveLine baseField) [IsFinite morphism] [Flat morphism]

/-- Polynomial basic opens of the target give a finite-free algebra of sections. -/
lemma free_finite_chartBasicOpen (coordinate : Fin 2) (polynomial : baseField[X]) :
    (letI := (morphism.app (chartBasicOpen baseField coordinate polynomial)).hom.toAlgebra;
      Module.Free Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial)
        Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial)) ∧
    (letI := (morphism.app (chartBasicOpen baseField coordinate polynomial)).hom.toAlgebra;
      Module.Finite Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial)
        Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial)) := by
  let := (polyToChartBasicOpen baseField coordinate polynomial).toAlgebra
  have := isLocalization_chartBasicOpen baseField coordinate polynomial
  refine ⟨?_, morphism.finite_app _ (isAffineOpen_chartBasicOpen baseField coordinate polynomial)⟩
  let := (morphism.app (chartBasicOpen baseField coordinate polynomial)).hom.toAlgebra
  by_cases zeroPolynomial : polynomial = 0
  · subst polynomial
    have := IsLocalization.uniqueOfZeroMem (M := Submonoid.powers (0 : baseField[X]))
      (S := Γ(projectiveLine baseField, chartBasicOpen baseField coordinate 0)) ⟨1, pow_one _⟩
    exact .of_subsingleton' _ _
  have := IsLocalization.isDomain_of_le_nonZeroDivisors
    Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial)
    (powers_le_nonZeroDivisors_of_noZeroDivisors zeroPolynomial)
  have := IsLocalization.isPrincipalIdealRing (Submonoid.powers polynomial)
    (S := Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial))
  exact morphism.free_app (isAffineOpen_chartBasicOpen baseField coordinate polynomial)

end AlgebraicGeometry.Scheme.Hom
