import ZInQKernel.Contrib.TYZGenus.ShimuraFricke
open ZInQ.Contrib.TYZGenus
#check @Shimura.etaModelFricke
#check @Shimura.theta_dup_half_sign
#check @Shimura.theta_parity_gen
#print axioms Shimura.etaModelFricke
#print axioms Shimura.etaModelEquation
#print axioms Shimura.etaModelInvariant
example : Package.TYZSigmaFixesZn ↔ Package.TYZSigmaFixesZn := Iff.rfl
#check fun hS => Shimura.tyzSigmaFixesZn_of (Shimura.shimuraReciprocityPic_of_shimuraModFn hS) Shimura.etaModelFricke
