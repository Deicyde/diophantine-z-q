import ZInQKernel.Contrib.OneProof.RC.KappaRational2.Jacobian
import ZInQKernel.Contrib.OneProof.RC.KappaRational2.Consumers
import ZInQKernel.Contrib.OneProof.RC.KappaRational2.WeakWeil
import Lean

open ZInQ.Manuscript.RC.KappaRational2
open Lean Elab Command

-- Print the two private theorems by their kernel names.
run_cmd do
  let mod := `ZInQKernel.Contrib.OneProof.RC.KappaRational2.Periods
  for n in #[`ZInQ.Manuscript.RC.KappaRational2.primitive_tendsto_translate,
      `ZInQ.Manuscript.RC.KappaRational2.lattice_submodule_alternatives] do
    elabCommand (← `(command| #print axioms $(mkIdent (mkPrivateNameCore mod n))))

#print axioms no_integral_period_scaling
#print axioms periodSubmodule
#print axioms scaled_periods_clear_lattice
#print axioms rational_of_reference_scale
#print axioms rational_of_matching_coeffs
#print axioms reference_scale_of_jacobian_values
#print axioms rational_of_jacobian_values
#print axioms prepared_values_of_reference_scale
#print axioms missing_values_of_reference_scale
#print axioms ring_values_of_reference_scale
#print axioms genus_values_of_reference_scale
#print axioms hElkikMD_of_reference_scale
#print axioms newformPeriodsRational_of_modularToWeakWeil
#print axioms rational_of_modularToWeakWeil
