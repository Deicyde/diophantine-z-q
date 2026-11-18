import ZInQKernel.Contrib.OneProof.AbVarQuotientConnected

/-! Axiom audit for the quotient glue. -/

open Lean Elab Command in
run_cmd do
  let privateRoot := Name.mkNum `_private.ZInQKernel.Contrib.OneProof.AbVarQuotientConnected 0
  for helper in
      [`ShimuraSteps.Quotient.componentModel_kernel,
       `ShimuraSteps.Quotient.openImmersion_of_closed_and_open_range,
       `ShimuraSteps.Quotient.residual_unit_open,
       `ShimuraSteps.Quotient.finite_of_open_kernel_unit] do
    elabCommand (← `(command| #print axioms $(mkIdent (privateRoot ++ helper))))

#print axioms ShimuraSteps.Quotient.schemeKernelConnected_of_kerConnected
#print axioms ShimuraSteps.Quotient.kerConnected_iff_schemeKernelConnected
