import ZInQKernel.Contrib.OneProof.AbVarQuotientComplement

/-! Axiom audit for the quotient glue. -/

open Lean Elab Command in
run_cmd do
  let privateRoot := Name.mkNum `_private.ZInQKernel.Contrib.OneProof.AbVarQuotientComplement 0
  for helper in
      [`ShimuraSteps.Quotient.intersection_isPullback,
       `ShimuraSteps.Quotient.factor_of_effectiveEpi,
       `ShimuraSteps.Quotient.descended_kernel] do
    elabCommand (← `(command| #print axioms $(mkIdent (privateRoot ++ helper))))

#print axioms ShimuraSteps.Quotient.abVarQuotientBySubvarietyExists
