import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed

#discharges

/-- The provider has exactly the field's type (definitional check by `example`, and the field's type printed). -/
example : AvSplit.MumfordTorsionAlgClosed := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
#check @ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
#print axioms ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
