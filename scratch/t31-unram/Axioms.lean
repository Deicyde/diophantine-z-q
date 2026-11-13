import ZInQKernel.Contrib.T31.Main

open GlueDescent.B2Q in
example : LeafUnramified := T31.leafUnramified

#check (T31.leafUnramified : GlueDescent.B2Q.LeafUnramified)
#print axioms T31.leafUnramified
#print axioms T31.signCob_of_cyclic_even
#print axioms T31.exists_base
#print axioms T31.exists_unramifiedExtension
