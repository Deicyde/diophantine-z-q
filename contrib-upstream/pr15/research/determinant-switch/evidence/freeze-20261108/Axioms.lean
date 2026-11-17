import Research.DerivativeSwitchBoundary
import Lean.Util.CollectAxioms
set_option pp.universes true
set_option pp.explicit true
#print Research.DerivativeSwitch.AxesKernel
#print Research.DerivativeSwitch.Volume.area
#print Research.DerivativeSwitch.Volume.action
#print axioms Research.DerivativeSwitch.finite_kernel_line
#print axioms Research.DerivativeSwitch.singular_kernel_line
#print axioms Research.DerivativeSwitch.boundary_images_meet_zero
#print axioms Research.DerivativeSwitch.no_identity_strict_square
#print axioms Research.DerivativeSwitch.Volume.area_action
#print axioms Research.DerivativeSwitch.Volume.area_neg_one
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[`Research.DerivativeSwitch.finite_kernel_line, `Research.DerivativeSwitch.singular_kernel_line, `Research.DerivativeSwitch.boundary_images_meet_zero, `Research.DerivativeSwitch.no_identity_strict_square, `Research.DerivativeSwitch.Volume.area_action, `Research.DerivativeSwitch.Volume.area_neg_one]
  for name in names do
    let declaration ← getConstInfo name
    logInfo m!"STATEMENT {name}: {declaration.type}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"
  logInfo "AXIOM_AUDIT_PASS declarations=6"
