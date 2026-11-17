import Solution
import Lean.Util.CollectAxioms
set_option pp.universes true
set_option pp.explicit true
#print Research.DerivativeSwitch.AxesKernel
#print Research.DerivativeSwitch.Volume.area
#print Research.DerivativeSwitch.Volume.action
#print Research.BoundaryScalar.axis
#print Research.BoundaryScalar.singularNormal
#print Research.BoundaryScalar.exchange
#print Research.BoundaryScalar.finiteNormal
#print Research.BoundaryCupAdapter.transportedPairing
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[`Research.DerivativeSwitch.finite_kernel_line, `Research.DerivativeSwitch.singular_kernel_line, `Research.DerivativeSwitch.boundary_images_meet_zero, `Research.DerivativeSwitch.no_identity_strict_square, `Research.DerivativeSwitch.Volume.area_action, `Research.DerivativeSwitch.Volume.area_neg_one, `Research.BoundaryScalar.adjugate_singularNormal, `Research.BoundaryScalar.adjugate_finiteNormal, `Research.BoundaryScalar.tensor_of_normal_form, `Research.BoundaryScalar.finite_tensor, `Research.BoundaryScalar.singular_tensor, `Research.BoundaryScalar.finite_cross_ne_zero, `Research.BoundaryScalar.singular_cross_ne_zero, `Research.BoundaryScalar.finite_coordinate_iff, `Research.BoundaryScalar.singular_coordinate_iff, `Research.BoundaryScalar.boundary_scalar_formula, `Research.BoundaryScalar.scalar_comparison, `Research.BoundaryScalar.normalized_scalar_comparison, `Research.BoundaryScalar.scalar_comparison_of_unit, `Research.BoundaryCupAdapter.cross_evaluations_eq, `Research.BoundaryCupAdapter.cross_evaluations_with_factors]
  for name in names do
    let declaration ← getConstInfo name
    logInfo m!"STATEMENT {name}: {declaration.type}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"
  logInfo "AXIOM_AUDIT_PASS declarations=21"
