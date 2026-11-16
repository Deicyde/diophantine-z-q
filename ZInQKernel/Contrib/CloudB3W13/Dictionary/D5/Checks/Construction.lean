import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.Construction

/-! Verification-only checks for the bounded FakeEC construction. Requires
normalizer's core cone with canonical existing main Galois providers. Not
imported by the production proof chain; not a complete D5/H119 check. -/

noncomputable section

#check ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelAct_trace
#check ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelFakeEC

example {K : Type} [Field K] [CharZero K] (P : LeafQM.AV.QML3 K) :
    ZInQ.Contrib.CloudB2Shimura.Dictionary.FakeEC K :=
  ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelFakeEC P

#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelAct_trace
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.identityLevelEquiv
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelFakeEC
#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.kernelFakeEC_act
