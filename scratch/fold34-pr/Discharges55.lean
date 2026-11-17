import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.GAGAMorphism

#discharges

/-- The provider has exactly the field's type. -/
example : ZInQ.HomLattice.GAGAMorphism := ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof
#check @ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof
#print axioms ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof
