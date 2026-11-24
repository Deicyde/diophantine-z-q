import ZInQKernel.Contrib.CloudR2Poincare.L6.ProductGeometry
import ZInQKernel.Contrib.CloudR2Poincare.L6.CubeClass
/-! Actual base hypotheses for the universal cube: the parameter is J itself,
never an arbitrary test T. No representability/model/cube premise is supplied. -/
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
namespace ZInQ.Contrib.CloudR2Poincare.L6

/-- The actual Jacobian/abelian-variety parameter is locally Noetherian. -/
theorem nativeAbVar_parameter_locallyNoetherian
    {k : Type u} [Field k] [CharZero k] (J : PkgI3.AbVar k) :
    IsLocallyNoetherian J.X.left := LocallyOfFiniteType.isLocallyNoetherian J.X.hom

/-- The actual parameter J is integral over its field, hence genuinely reduced. -/
theorem nativeAbVar_parameter_reduced
    {k : Type u} [Field k] [CharZero k] (J : PkgI3.AbVar k) :
    AlgebraicGeometry.IsReduced J.X.left := by
  haveI : AlgebraicGeometry.IsIntegral J.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton J.X.hom
  infer_instance

/-- Connectedness belongs to the actual parameter J, not to arbitrary test P. -/
theorem nativeAbVar_parameter_connected
    {k : Type u} [Field k] [CharZero k] (J : PkgI3.AbVar k) :
    ConnectedSpace J.X.left := by
  haveI : AlgebraicGeometry.IsIntegral J.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton J.X.hom
  infer_instance

/-- Actual proper/geometric-integrality of the double factor used over parameter J. -/
theorem nativeAbVar_doubleFactor_geometry
    {k : Type u} [Field k] [CharZero k] (J : PkgI3.AbVar k) :
    IsProper (J.X ⊗ J.X).hom ∧ GeometricallyIntegral (J.X ⊗ J.X).hom := by
  haveI : IsProper (fst J.X J.X).left :=
    inferInstanceAs (IsProper (pullback.fst J.X.hom J.X.hom))
  have hp : IsProper (J.X ⊗ J.X).hom := by rw [← Over.w (fst J.X J.X)]; infer_instance
  exact ⟨hp, nativeProduct_geometricallyIntegral J.X J.X⟩

end ZInQ.Contrib.CloudR2Poincare.L6
