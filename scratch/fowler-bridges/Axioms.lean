import ZInQKernel.Contrib.OneProof.FowlerBridgesForms

#print axioms HDec.CMBranch.FowlerBridges.toOrder
#print axioms HDec.CMBranch.FowlerBridges.exists_intBasis_of_isImagQuadOrder
#print axioms HDec.CMBranch.FowlerBridges.toOrder_index_eq_conductor
#print axioms HDec.CMBranch.FowlerBridges.orderDisc_eq_discr
#print axioms HDec.CMBranch.FowlerBridges.orderDisc_neg
#print axioms HDec.CMBranch.FowlerBridges.discr_intBasis_mod_four
#print axioms HDec.CMBranch.FowlerBridges.orderDisc_mod_four
#print axioms HDec.CMBranch.FowlerBridges.finite_pic
#print axioms HDec.CMBranch.FowlerBridges.card_pic_pos
#print axioms HDec.CMBranch.FowlerBridges.exists_fractionalIdeal_basis
#print axioms HDec.CMBranch.FowlerBridges.proper_iff_isUnit
#print axioms HDec.CMBranch.FowlerBridges.properIdealClassesEquivClassGroup
#print axioms HDec.CMBranch.FowlerBridges.finite_properIdealClasses
#print axioms HDec.CMBranch.FowlerBridges.card_pic_eq_properClassNumber
#print axioms HDec.CMBranch.FowlerBridges.fowlerProp27_of_print
#print axioms HDec.CMBranch.FowlerBridges.PrimitivePositiveForm.four_mul_eval
#print axioms HDec.CMBranch.FowlerBridges.PrimitivePositiveForm.eval_pos
#print axioms HDec.CMBranch.FowlerBridges.properFormSetoid_iff
#print axioms HDec.CMBranch.FowlerBridges.card_pic_eq_card_properFormClasses_of

open Lean Elab Command in
run_cmd do
  for lemmaName in #[`HDec.CMBranch.FowlerBridges.exists_noninteger,
      `HDec.CMBranch.FowlerBridges.mul_mem_of_mem_pair] do
    let name := mkPrivateNameCore `ZInQKernel.Contrib.OneProof.FowlerBridgesIdeals lemmaName
    elabCommand (← `(command| #print axioms $(mkIdent name):ident))
