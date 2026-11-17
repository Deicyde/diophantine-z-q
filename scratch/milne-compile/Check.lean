import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.MilneIsogenyQuasiInverse

example : _root_.AvSplit.MilneIsogenyQuasiInverse =
    _root_.AvSplit.MilneIsogenyQuasiInverse := rfl
example : (_root_.AvSplit.MilneIsogenyQuasiInverse : Prop) := 
  ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof
#check (ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof :
  _root_.AvSplit.MilneIsogenyQuasiInverse)
#print axioms ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof

#discharges
