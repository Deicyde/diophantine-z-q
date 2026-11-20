import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ScopedConsumer
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ScopedInventory

open Lean in
macro "#print_private_axioms" mod:ident decl:ident : command =>
  `(#print axioms $(mkCIdent (mkPrivateNameCore mod.getId decl.getId)))

#print axioms ZInQ.Manuscript.RC.EvenJoin.FixedPlaceExtension
#print axioms ZInQ.Manuscript.RC.EvenJoin.FixedPlaceExtension.apply_ringMap
#print axioms ZInQ.Manuscript.RC.EvenJoin.FixedPlaceExtension.two_pow_dvd_iff
#print axioms ZInQ.Manuscript.RC.EvenJoin.FixedPlaceExtension.reduce_eq_zero_iff
#print axioms ZInQ.Manuscript.RC.EvenJoin.FixedPlaceExtension.source
#print axioms ZInQ.Manuscript.RC.EvenJoin.fixedH
#print axioms ZInQ.Manuscript.RC.EvenJoin.fixed_numerator_dvd
#print axioms ZInQ.Manuscript.RC.EvenJoin.coordinate_match_of_seed_scoped
#print axioms ZInQ.Manuscript.RC.EvenJoin.map_fixed_theta
#print axioms ZInQ.Manuscript.RC.EvenJoin.evenExpansion_joined_scoped
#print axioms ZInQ.Manuscript.RC.EvenJoin.HeckeAt
#print axioms ZInQ.Manuscript.RC.EvenJoin.LocalAt
#print axioms ZInQ.Manuscript.RC.EvenJoin.BudgetRealizationScoped
#print axioms ZInQ.Manuscript.RC.EvenJoin.budgetRealization_of_joined_scoped
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.ScopedConsumer ZInQ.Manuscript.RC.EvenJoin.residue_of_dvd_two
#print axioms ZInQ.Manuscript.RC.EvenJoin.coefficient_one_scoped
#print axioms ZInQ.Manuscript.RC.EvenJoin.trace_join_at
#print axioms ZInQ.Manuscript.RC.EvenJoin.fixedU_of_joined_scoped
#print axioms ZInQ.Manuscript.RC.EvenJoin.primary_of_joined_scoped
#print axioms ZInQ.Manuscript.RC.EvenJoin.unitSeed_of_joined_scoped
#print axioms ZInQ.Manuscript.RC.EvenJoin.rules_and_seed_of_joined_scoped
#print axioms ZInQ.Manuscript.RC.EvenJoin.finite_constituent_compositum
#print axioms ZInQ.Manuscript.RC.EvenJoin.evenSeed_coeff_fixedRing
