import ZInQKernel.Contrib.LocalKW.LocalKW

#check @ZInQ.Contrib.localKroneckerWeber
#print axioms ZInQ.Contrib.localKroneckerWeber
#print axioms ZInQ.Contrib.LocalKW.le_adjoin_rootsOfUnity
#print axioms ZInQ.Contrib.LocalKW.le_of_normGroup_le
#print axioms ZInQ.Contrib.LocalKW.fixes_of_mem_normGroup
#print axioms ZInQ.Contrib.LocalKW.normGroup_cyclotomic_le_powerSubgroup
#print axioms ZInQ.Contrib.LocalKW.exists_pow_eq_of_norm_sub_one_le
#print axioms ZInQ.Contrib.LocalKW.exists_eq_zpow_mul_unit
#print axioms ZInQ.Contrib.LocalKW.valuation_unit
#print axioms ZInQ.Contrib.LocalKW.artinGal_eq_one_of_mem
#print axioms ZInQ.Contrib.LocalKW.localArtinMap_eq_artinGal
#print axioms ZInQ.Contrib.LocalKW.coprime_self_pow_sub_one
#print axioms ZInQ.Contrib.LocalKW.zpow_apply_eq_self
#print axioms ZInQ.Contrib.LocalKW.norm_natCast_padicInt
#print axioms ZInQ.Contrib.LocalKW.coe_sepIncl
example (p : ℕ) [Fact p.Prime] : PkgI6.LocalKroneckerWeber p := ZInQ.Contrib.localKroneckerWeber p
