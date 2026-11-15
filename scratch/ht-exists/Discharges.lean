import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.EigenformHTExists

#discharges

#print axioms EigenformHTExists.eigenformHTNew_of_katoHTExists
#print axioms EigenformHTExists.katoHTExists_of_eigenformHTNew
#print axioms EigenformHTExists.katoHTExists_iff
#print axioms EigenformHTExists.eigenformHTNew5Ge3_of_katoHTExists5Ge3
#print axioms EigenformHTExists.katoHTExists5Ge3_of_eigenformHTNew5Ge3
#print axioms EigenformHTExists.eigenformHT5Ge3Chain_of_katoHTExists5Ge3
#print axioms EigenformHTExists.htDual_proof

example : EigenformHTExists.KatoHTExists → HDec.HSyn.OpenAddedLeaves17 → ZInQ.Contrib.HodgeSplit.EigenformHTNew :=
  fun h l => EigenformHTExists.eigenformHTNew_of_katoHTExists h l.tateTwistInvariants l.axSenTate
#print axioms HDec.HSyn.G0AssembleMod.afterG7_of3Kato5
