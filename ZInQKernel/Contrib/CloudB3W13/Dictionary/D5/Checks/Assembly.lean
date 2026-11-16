import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.Count

/-!
Verification-only checks for the complete D5 converse.
These require the normalized recovered trace/cardinality dependency cones.
This file is not imported by the production chain, and is not a completed
verification claim until it has actually been compiled.
-/

#check ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.d5_obligation

example : ZInQ.Contrib.CloudB2Shimura.Dictionary.D5_Obligation :=
  ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.d5_obligation

#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelAct_trace
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelFakeEC
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.algLevel_torsion_card
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelFullLevel
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelLaw_roundtrip
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.d5_obligation
