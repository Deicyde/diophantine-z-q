import ZInQKernel.Contrib.OneProof.FowlerUnique

open HDec.CMBranch.FowlerBridges

#print axioms quadraticAlgebra_basis_discr
#print axioms order_finrank_eq_two
#print axioms order_discr_mod_four
#print axioms orders_ringEquiv_of_discr_eq
#print axioms fields_ringEquiv_of_order_discr_eq
#print axioms fields_ringEquiv_of_discr_eq
#print axioms discr_and_index_eq_of_order_discr_eq
#print axioms index_sq_eq_discr_ediv
#print axioms mem_order_iff_intCast_add_index_smul
#print axioms mem_isImagQuadOrder_iff
#print axioms map_order_of_index_eq

#print axioms properClassNumber_ringEquiv
#print axioms properClassNumber_eq_of_discr_eq
#print axioms hDelta
#print axioms hDelta_eq_properClassNumber
#print axioms field_ringEquiv_sqrt_orderDiscr
#print axioms field_ringEquiv_sqrt_discr
#print axioms isFundamentalDiscr_field
#print axioms FowlerProp27PrintCanonical
#print axioms fowlerProp27Print_of_canonical
#print axioms fowlerProp27Print_iff_canonical
#print axioms fowlerProp27_of_canonical

open Lean Elab Command in
run_cmd do
  for decl in #[`HDec.CMBranch.FowlerBridges.exists_basis_one,
      `HDec.CMBranch.FowlerBridges.basis_discr,
      `HDec.CMBranch.FowlerBridges.exists_order_algEquiv] do
    let name := mkPrivateNameCore `ZInQKernel.Contrib.OneProof.FowlerUniqueDiscriminant decl
    elabCommand (← `(command| #print axioms $(mkIdent name):ident))

open Lean Elab Command in
run_cmd do
  for decl in #[`HDec.CMBranch.FowlerBridges.picEquiv,
      `HDec.CMBranch.FowlerBridges.modelDiscr,
      `HDec.CMBranch.FowlerBridges.modelNonsquare,
      `HDec.CMBranch.FowlerBridges.modelIntNonsquare,
      `HDec.CMBranch.FowlerBridges.modelNumberField,
      `HDec.CMBranch.FowlerBridges.modelTotallyComplex,
      `HDec.CMBranch.FowlerBridges.canonicalOrder,
      `HDec.CMBranch.FowlerBridges.canonicalOrder_discr,
      `HDec.CMBranch.FowlerBridges.fieldDiscrNeg] do
    let name := mkPrivateNameCore `ZInQKernel.Contrib.OneProof.FowlerUnique decl
    elabCommand (← `(command| #print axioms $(mkIdent name):ident))
