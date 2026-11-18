import ZInQKernel.Contrib.OneProof.AbVarQuotientFinite

/-! Axiom audit for the quotient glue. -/

open Lean Elab Command in
run_cmd do
  let privateRoot := Name.mkNum `_private.ZInQKernel.Contrib.OneProof.AbVarQuotientFinite 0
  for helper in
      [`ShimuraSteps.Quotient.target_pair_mono,
       `ShimuraSteps.Quotient.target_properties,
       `ShimuraSteps.Quotient.finiteSchemeQuotient,
       `ShimuraSteps.Quotient.exists_operations,
       `ShimuraSteps.Quotient.separated_quotient,
       `ShimuraSteps.Quotient.translation_kernel] do
    elabCommand (← `(command| #print axioms $(mkIdent (privateRoot ++ helper))))

#print axioms ShimuraSteps.Quotient.finiteSubgroupQuotient_exists
