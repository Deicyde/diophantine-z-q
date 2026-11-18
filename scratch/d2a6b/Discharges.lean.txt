import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.D2A6Chain

/-! d2a6b (d2a6-reroute's check, on f3402e89): `#discharges` over the base's `frozenTarget` with this task's modules
imported, and `#print axioms` of every theorem of the four d2a6-reroute files and A6Z30 (d2a6b), and of the generated
chain's top. The fold's top `sixContactMin_of_open77` is in scratch/d2a6b/BypassFold.lean (bypass-out.txt). -/

#discharges

#print axioms HDec.G15Ram.isWildInertia_of_wild_gen
#print axioms HDec.G15Ram.raynaudPlace_of_fix
#print axioms HDec.G15Ram.raynaudPlaceFix_of_wildNF
#print axioms HDec.G15Ram.raynaudPlace_of_wildNF
#print axioms HDec.G15Ram.torsFixWild_of_raynaudFix
#print axioms HDec.G15Ram.tateWildK_of_wildNF
#print axioms HDec.G15Ram.localGlue_of_leaves_wildNF
#print axioms HDec.G15Ram.torsFix_of_wildNF
#print axioms HDec.G15Ram.torsFixWildOdd_of_wildNF
#print axioms HDec.G15Ram.torsFixWildE_of_twist_wildNF
#print axioms HDec.G15Ram.tateWildKE_of_wildNF
#print axioms HDec.G15Ram.localGlue_of_descent_wildNF
#print axioms D2A6.map_left_fst'
#print axioms D2A6.eta_pullback_fst
#print axioms D2A6.isUnit_of_not_dvd
#print axioms D2A6.hasGoodReduction_of_intModel
#print axioms HDec.LTGoodRed.goodRedTorsionT
#print axioms HDec.D2A6.lt_of_notMem_T324
#print axioms HDec.D2A6.T324_subset_T
#print axioms HDec.D2A6.qmModelG3U_of
#print axioms HDec.D2A6.modelG3G6_of_U
#print axioms HDec.D2A6.modelG3G6_of_leavesU
#print axioms HDec.G15Ram.raynaudPlace_of_R6U
#print axioms HDec.G15Ram.tateWildK_of_R6U
#print axioms HDec.G15Ram.torsFix_of_R6U
#print axioms HDec.HSyn.modelG3G6_of_leaves3U
#print axioms HDec.G0ModField.KernelField.good_of_QML3U
#print axioms D2A6.spec_to_Z30_ext
#print axioms D2A6.not_dvd_thirty_of_lt
#print axioms D2A6.z30ToLocal
#print axioms D2A6.hasGoodReduction_of_z30
#print axioms HDec.D2A6.qmModelG3U_of_z30
#print axioms HDec.D2A6.modelG3G6_of_leavesU_z30
#print axioms HDec.HSyn.sixContactMin_of_open73_u
