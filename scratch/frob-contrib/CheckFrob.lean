import ZInQKernel.Contrib.AbsFrob.AlgFrobRed
import ZInQKernel.Contrib.AbsFrob.Sanity
import ZInQKernel.Contrib.UnramRoots.Main
import ZInQKernel.Contrib.UnramRoots.Sanity

/-! Axiom check of the modules adopted by task frob-contrib only (the full check is Check.lean). -/

#print axioms AbsFrobDef.fr
#print axioms AbsFrobDef.fr_naturality
#print axioms AbsFrobDef.fr_Spec
#print axioms AbsFrobDef.fr_naturality'
#print axioms AbsFrobDef.fr_Spec_zmod
#print axioms AbsFrobDef.fr_Spec_polynomial_ne_id
#print axioms AlgFrobRedRed.absFrob
#print axioms UnramRootsTask.unramRoots
#print axioms UnramRootsTask.unramRoots_all
#print axioms UnramRootsTask.unramRoots_two
#print axioms UnramRootsTask.unramProcyclic_of_frobData
#print axioms UnramRootsTask.frobData_exists
#print axioms UnramRootsTask.Sanity.unramRoots_two_nonvacuous
