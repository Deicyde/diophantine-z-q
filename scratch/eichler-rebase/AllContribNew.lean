-- eichler-rebase step (2): every module of ZInQKernel/Contrib/ on main (ZInQKernel.Contrib.AllContrib, stab-clash's
-- list, 3047 imports) together with the modules this branch adds (R5fpCountLe imports EichlerBound/* and
-- GR56Lattice; GRDict is gr-dict's module, also absent from main). Elaborates iff no name clashes.
import ZInQKernel.Contrib.AllContrib
import ZInQKernel.Contrib.OneProof.GR56Lattice
import ZInQKernel.Contrib.OneProof.R5fpCountLe
import ZInQKernel.Contrib.OneProof.GRDict

#check @EichlerBound.r5fpCountLe_proof
#check @EichlerBound.eichlerOptEmbBound6
#print axioms EichlerBound.r5fpCountLe_proof
