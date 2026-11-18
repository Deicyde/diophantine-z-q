import ZInQKernel.Contrib.OneProof.C8CFT
import ZInQKernel.Contrib.OneProof.C8Ladic
#check @Valuation.isEquiv_valuation_valuationSubring
#check @Valuation.IsEquiv.lt_one_iff
#check @IsCompact.inter_iInter_nonempty
#check @HDec.G0Galois.C8Conrad.Ladic.exists_lift
#check @HDec.G0Galois.C8Conrad.Ladic.decomp_spec
#check @Padic.natCard_residueField
example (p : ℕ) [Fact p.Prime] : CompactSpace (PkgI4.GQp p) := inferInstance
#check @stabilizer_isOpen_of_isIntegral
#print GlueDescent.B2Q.GQ
#check @IsPrimitiveRoot.eq_pow_of_pow_eq_one
#check @IsPrimitiveRoot.map_of_injective
#print PkgI4.decomp
#check @Valuation.mem_valuationSubring_iff
