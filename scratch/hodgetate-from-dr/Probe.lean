import ZInQKernel.OneProof.H.TailX
set_option pp.fullNames true
#check @HDec.HSyn.tatePairingZl_of_leaves4
#check @HDec.HSyn.tateModuleFree_of_t5'
#check @HDec.HSyn.toAbVarK4
#check @HDec.HSyn.torsionStructureK_of4
#check @T5Torsion.TateFree.tate_surj_of_torsionStructure
#check @HDec.WeilPairing.tmuCoordLin_injective
#check @HDec.WeilPairing.tatePairing_self
#print HDec.WeilPairing.SymmIsogeny
#check @HDec.G0Galois.skew_of_alt'
#check @ZInQ.Contrib.G9.PkgI4.htAct_apply
#check @ZInQ.Contrib.G9.PkgI4.cycPow_add_one
#check @ZInQ.Contrib.G9.PkgI4.cycPow_one_ne_zero
#check @ZInQ.Contrib.HodgeSplit.finrank_fixSp_range
#check @ZInQ.Contrib.HodgeSplit.fd_fixSp_range
#check @ZInQ.Contrib.AbVarBC.galK
#check @LinearMap.BilinForm.toDual
#check @dualTensorHomEquiv
example (p : ℕ) [Fact p.Prime] : PadicAlgCl p = AlgebraicClosure ℚ_[p] := rfl
