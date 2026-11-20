import ZInQKernel.Contrib.OneProof.RC.EvenJoin.Coordinates

open Lean in
macro "#print_private_axioms" mod:ident decl:ident : command =>
  `(#print axioms $(mkCIdent (mkPrivateNameCore mod.getId decl.getId)))

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.Joined ZInQ.Manuscript.RC.EvenJoin.unary_on_subscripts
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.Joined ZInQ.Manuscript.RC.EvenJoin.exists_joinedForm
#print axioms ZInQ.Manuscript.RC.EvenJoin.joinedForm
#print axioms ZInQ.Manuscript.RC.EvenJoin.joinedForm_coeff
#print axioms ZInQ.Manuscript.RC.EvenJoin.evenExpansion_joined
#print axioms ZInQ.Manuscript.RC.EvenJoin.budgetRealization_of_joined
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.Coordinates ZInQ.Manuscript.RC.EvenJoin.map_moving
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.Coordinates ZInQ.Manuscript.RC.EvenJoin.map_unary
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.Coordinates ZInQ.Manuscript.RC.EvenJoin.map_theta
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.Coordinates ZInQ.Manuscript.RC.EvenJoin.moving_zero
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.Coordinates ZInQ.Manuscript.RC.EvenJoin.unary_zero
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.Coordinates ZInQ.Manuscript.RC.EvenJoin.unitCharacter_lift
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.Coordinates ZInQ.Manuscript.RC.EvenJoin.movingCharacter_lift
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.Coordinates ZInQ.Manuscript.RC.EvenJoin.unaryCharacter_lift
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.Coordinates ZInQ.Manuscript.RC.EvenJoin.blockCoordinates
#print axioms ZInQ.Manuscript.RC.EvenJoin.evenCoordinates
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.Coordinates ZInQ.Manuscript.RC.EvenJoin.exists_evenSeed
#print axioms ZInQ.Manuscript.RC.EvenJoin.evenSeed
#print axioms ZInQ.Manuscript.RC.EvenJoin.evenSeed_eval
#print axioms ZInQ.Manuscript.RC.EvenJoin.coordinate_match_of_seed
#print axioms ZInQ.Manuscript.RC.EvenJoin.no_common_level
