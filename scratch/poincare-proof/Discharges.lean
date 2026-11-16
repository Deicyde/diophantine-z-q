import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.PoincareComplement

#discharges

#print axioms ZInQ.Contrib.OneProof.PoincareComplement.poincareComplement_of_open

example : ZInQ.Contrib.AVB1.PoincareComplement → HDec.HSyn.OpenTextbookLeaves12 → True := fun _ _ => trivial
