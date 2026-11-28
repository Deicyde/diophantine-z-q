import ZInQKernel.Contrib.OneProof.CMHeight62Full.TreeH3

/-!
# cmHeight62 (finite place): the axioms of the tree wiring, part B (items H3 and H4)

Prints the axioms of every declaration of `TreeH3.lean` and `TreeH4.lean`. Expected:
`[propext, Classical.choice, Quot.sound]` or a subset.
-/

namespace ZInQ.Contrib.CMHeight62Full

-- item H4 (TreeH4.lean)
#print axioms tree34_exists_ord_one
#print axioms tree34_mem_sq_of_two_le_ord
#print axioms tree34_ord_eq_one_of_not_mem_sq
#print axioms tree34_valuation_of_ord
#print axioms tree34_ord_map_eq_zero
#print axioms tree34_ord_xy
#print axioms tree34_ringEquiv_mem_maximalIdeal
#print axioms tree34_mem_sq_of_ringEquiv
#print axioms tree34_stalkEquivIntegers
#print axioms tree34_stalkEquivIntegers_coe
#print axioms tree34_ord_algebraMap_eq_one
#print axioms tree34_mem_sq_of_ord
#print axioms tree34_toHodgeOne_eq_div_smul
#print axioms tree34_wedge_eq_smul_of_sub_mem_sq
#print axioms tree34_wedge_eq_smul_line
#print axioms tree34_comparison_of_wedge
#print axioms treeH4_etaW_eq
#print axioms treeH4_abVarIdentity_eq
#print axioms treeH4_tG_not_mem_sq
#print axioms treeH4_originStalkEquiv_tG
#print axioms treeH4_tL_not_mem_sq
#print axioms treeH4_ord_tL
#print axioms treeH4_mem_sq_of_ord
#print axioms treeH4_etaW_eq_smul
#print axioms treeH4_comparison

-- item H3 (TreeH3.lean)
#print axioms tree34_injective_of_isIso
#print axioms tree34_eq_of_fst_eq
#print axioms tree34_functionFieldMap_const
#print axioms treeH3_bcProj_isDominant
#print axioms treeH3Iota
#print axioms treeH3Iota_algebraMap_stalk
#print axioms treeH3Iota_algebraMap
#print axioms treeH3Iota_ne_zero
#print axioms treeH3Iota_integers
#print axioms treeH3Iota_fXY
#print axioms treeH3_Y_sq
#print axioms treeH3_equation
#print axioms treeH3_ord
#print axioms treeH3_valuation
#print axioms treeH3_regularAway
#print axioms treeH3_param
#print axioms treeH3_poleSpaces
#print axioms treeH3_n11Inst
#print axioms treeH3_exists_variableChange

end ZInQ.Contrib.CMHeight62Full
