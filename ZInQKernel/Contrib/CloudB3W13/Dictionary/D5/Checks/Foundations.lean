import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.FiniteLevel
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.KernelGroup
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.GeometricPoints
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.Transport
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.Checks.Transport

/-! Verification-only checks for the independently built D5 foundations.
Not imported by the production proof chain. -/

#check ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.representatives_injective
#check ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.geometricEta_ker
#check ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.objectOfEq_iso

#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.representatives_injective
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.eta_surjective_of_torsion_card
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelLaw_comm
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernel_bundle
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelPt_mul
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelPt_one
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelIdentity_closed
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.geometricPointsMap_injective
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.geometricEta_ker
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.qmOfEq_hom
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.levelOfEq_pt
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.objectOfEq_iso
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.TransportCheck.fixed_carrier
