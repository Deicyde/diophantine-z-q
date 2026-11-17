import Solution
import Lean.Util.CollectAxioms
set_option pp.universes true
set_option pp.explicit true
#print Research.DerivativeSwitch.ScalarRatio.tensor
#print Research.DerivativeSwitch.ScalarRatio.HasCoordinate
#print Research.DerivativeSwitch.ScalarRatio.normal
#print Research.DerivativeSwitch.ScalarRatio.Index
#print Research.DerivativeSwitch.ScalarRatio.Local
#print Research.DerivativeSwitch.ScalarRatio.join
#print Research.DerivativeSwitch.ScalarRatio.pairCols
#print Research.DerivativeSwitch.ScalarRatio.area
#print Research.DerivativeSwitch.ScalarRatio.cycle
#print Research.DerivativeSwitch.ScalarRatio.frame
#print Research.DerivativeSwitch.ScalarRatio.target
#print Research.DerivativeSwitch.ScalarRatio.matrixUnit
#print Research.DerivativeSwitch.ScalarRatio.CommonStrictData
#print Research.DerivativeSwitch.ScalarRatio.CommonStrictData.delta
#print Research.DerivativeSwitch.ScalarRatio.CommonStrictData.eta
#print Research.DerivativeSwitch.ScalarRatio.CommonStrictData.a
#print Research.DerivativeSwitch.ScalarRatio.CommonStrictData.b
#print Research.DerivativeSwitch.ScalarRatio.CommonStrictData.theta
#print Research.DerivativeSwitch.ScalarRatio.CommonStrictData.qF
#print Research.DerivativeSwitch.ScalarRatio.CommonStrictData.qS
#print Research.DerivativeSwitch.ScalarRatio.unitValue
#print Research.DerivativeSwitch.ScalarRatio.UnitRelated
#print Research.DerivativeSwitch.ScalarRatio.finiteFormula
#print Research.DerivativeSwitch.ScalarRatio.singularFormula
#print Research.DerivativeSwitch.ScalarRatio.beta
#print Research.DerivativeSwitch.ScalarRatio.BoundaryCupIdentity
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[`Research.DerivativeSwitch.finite_kernel_line, `Research.DerivativeSwitch.singular_kernel_line, `Research.DerivativeSwitch.boundary_images_meet_zero, `Research.DerivativeSwitch.no_identity_strict_square, `Research.DerivativeSwitch.Volume.area_action, `Research.DerivativeSwitch.Volume.area_neg_one, `Research.BoundaryScalar.adjugate_singularNormal, `Research.BoundaryScalar.adjugate_finiteNormal, `Research.BoundaryScalar.tensor_of_normal_form, `Research.BoundaryScalar.finite_tensor, `Research.BoundaryScalar.singular_tensor, `Research.BoundaryScalar.finite_cross_ne_zero, `Research.BoundaryScalar.singular_cross_ne_zero, `Research.BoundaryScalar.finite_coordinate_iff, `Research.BoundaryScalar.singular_coordinate_iff, `Research.BoundaryScalar.boundary_scalar_formula, `Research.BoundaryScalar.scalar_comparison, `Research.BoundaryScalar.normalized_scalar_comparison, `Research.BoundaryScalar.scalar_comparison_of_unit, `Research.BoundaryCupAdapter.cross_evaluations_eq, `Research.BoundaryCupAdapter.cross_evaluations_with_factors, `Research.DerivativeSwitch.ScalarRatio.coordinate_of_frame, `Research.DerivativeSwitch.ScalarRatio.coordinate_of_closed_frame, `Research.DerivativeSwitch.ScalarRatio.adjugate_ne_zero_of_frame, `Research.DerivativeSwitch.ScalarRatio.coordinate_unique, `Research.DerivativeSwitch.ScalarRatio.raw_side_coordinate, `Research.DerivativeSwitch.ScalarRatio.common_strict_coordinate_formula, `Research.DerivativeSwitch.ScalarRatio.CommonStrictData.coordinate_values, `Research.DerivativeSwitch.ScalarRatio.transported_ratio, `Research.DerivativeSwitch.ScalarRatio.transported_unit_criterion, `Research.DerivativeSwitch.ScalarRatio.integral_unit_criterion, `Research.DerivativeSwitch.ScalarRatio.CommonStrictData.actual_coordinate_ratio, `Research.DerivativeSwitch.ScalarRatio.CommonStrictData.actual_integral_unit_criterion, `Research.DerivativeSwitch.ScalarRatio.boundary_cup_cross_evaluations, `Research.DerivativeSwitch.ScalarRatio.normalization_defect, `Research.DerivativeSwitch.ScalarRatio.common_normalization_adapter, `Research.DerivativeSwitch.ScalarRatio.det_neg_one_common_normalization, `Research.DerivativeSwitch.ScalarRatio.integral_boundary_cup_adapter, `Research.DerivativeSwitch.ScalarRatio.valuation_equal_of_unitRelated]
  for name in names do
    let declaration ← getConstInfo name
    logInfo m!"STATEMENT {name}: {declaration.type}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"
  logInfo "AXIOM_AUDIT_PASS declarations=39"
