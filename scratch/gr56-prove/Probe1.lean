import ZInQKernel.Contrib.OneProof.QMLattice
import ZInQKernel.Contrib.OneProof.GRCountX6

open CategoryTheory AlgebraicGeometry Limits

#check @ZInQ.LeafPush2.CPts
#check @ZInQ.LeafPush2.IsUniformization
#check @HDec.HSyn.G0Split.FibreQM.UniformizationExistsT35
#check @HDec.HSyn.G0Split.FibreQM.unif_ring_hom
#check @HDec.HSyn.G0Split.FibreQM.QMLatticeAlgebra
#check @HDec.G0ModField.KernelField.endBC
#check @HDec.G0ModField.KernelField.endBC_injective
#check @HDec.AVB2.t11b_of_exists
#check @HDec.HSyn.t11bExists_lf8
#check @AvSplit.Final.h69
#check @AvSplit.Final.h38
#check @HDec.FibreQMNorm.qmOrbit
#check @HDec.QMLattice.act_inj
#check @HDec.QMLattice.commutant
#check @HDec.QMLattice.act_algebraMap
#check @PkgI3.AbVar.dim_baseChange
#check @GRCountX6.EichlerOptEmbCount6
#check @AddSubgroup.nsmul_relIndex_mem
example {A B C : PkgI3.AbVar ℚ} (f : PkgI3.AbVar.Hom A B) (g : PkgI3.AbVar.Hom B C) : IsMonHom (f.hom ≫ g.hom) := inferInstance
