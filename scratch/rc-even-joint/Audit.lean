import ZInQKernel.Contrib.OneProof.RC.EvenJoin.JointConsumer
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.JointPlace

open Lean in
macro "#print_private_axioms" mod:ident decl:ident : command =>
  `(#print axioms $(mkCIdent (mkPrivateNameCore mod.getId decl.getId)))

#print axioms ZInQ.Manuscript.RC.EvenJoin.jointCut
#print axioms ZInQ.Manuscript.RC.EvenJoin.fixingSubgroup_jointCut
#print axioms ZInQ.Manuscript.RC.EvenJoin.joint_restriction_surjective
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.JointQuotient ZInQ.Manuscript.RC.EvenJoin.inertia_fixes_cut
#print axioms ZInQ.Manuscript.RC.EvenJoin.joint_frobenius
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.JointPlace ZInQ.Manuscript.RC.EvenJoin.valuationAbsoluteValue
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.JointPlace ZInQ.Manuscript.RC.EvenJoin.spectralNorm_eq_valuation_of_algHom
#print axioms ZInQ.Manuscript.RC.EvenJoin.finite_valued_compositum
#print axioms ZInQ.Manuscript.RC.EvenJoin.fixed_place_joint_extension
#print axioms ZInQ.Manuscript.RC.EvenJoin.evenOmissionSign
#print axioms ZInQ.Manuscript.RC.EvenJoin.evenOmissionSign_flip
#print axioms ZInQ.Manuscript.RC.EvenJoin.omission_reading_scoped
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.JointConsumer ZInQ.Manuscript.RC.EvenJoin.exists_character_cut
#print axioms ZInQ.Manuscript.RC.EvenJoin.reduced_trace_of_class
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.JointConsumer ZInQ.Manuscript.RC.EvenJoin.reading_eq_orbit_one
#print axioms ZInQ.Manuscript.RC.EvenJoin.o12_of_joined_scoped
#print axioms ZInQ.Manuscript.RC.EvenJoin.rules_and_seed_of_joined_joint
