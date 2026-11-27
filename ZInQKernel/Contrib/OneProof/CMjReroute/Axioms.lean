import ZInQKernel.Contrib.OneProof.CMjReroute.Descent
import ZInQKernel.Contrib.OneProof.CMjReroute.Consumer

/-! # Axiom check for the reroute trial: every result below must print only
`propext`, `Classical.choice`, `Quot.sound`. -/

open HDec.CMBranch.CMjReroute

-- restriction to the matrix-unit curve
#print axioms exists_lift_of_comm
#print axioms exists_restrict
#print axioms restrict_unique
#print axioms restrictHom
#print axioms restrictHom_spec
#print axioms eq_zero_of_mul_unit_eq_zero
#print axioms end_eq_zero_of_natCast_mul
#print axioms matrixUnit_restrict
#print axioms exists_le_of_center
-- the CM dictionary
#print axioms exists_eq_add_smul_of_commute
#print axioms mem_range_of_eig
#print axioms endOf_spec
#print axioms endOf_mem_center
#print axioms endHom_injective
#print axioms exists_endOf_eq
#print axioms comEquiv
#print axioms homLatticeCorr_proved
#print axioms comEquivCM
#print axioms comEquivCM_spec
#print axioms comEquivCM_mem_center
#print axioms exists_int_of_inO_rat
#print axioms eq_zero_of_eig_real
#print axioms liftM_intCast
#print axioms exists_cmPoint
-- the ring-class kernel
#print axioms saturation
#print axioms exists_bezout
#print axioms exists_int_add_index_mul
#print axioms ringClassIdeleQuotient_mk_eq_one
#print axioms ideleClassArtinMap_ringClassField_eq_one
#print axioms comap_le_integralClosure
#print axioms conductor_comap_ne_zero
#print axioms ringClassIdeleQuotient_mk_eq_one'
#print axioms ideleClassArtinMap_ringClassField_eq_one'
-- the orbit bound
#print axioms mem_range_of_mobPM_fix
#print axioms artin_trivial_of_eq
#print axioms artin_trivial_of_galPt_fix
#print axioms exists_extend_gal
#print axioms card_gal_le_ncard
#print axioms card_pic_le_ncard
#print axioms card_pic_le_324
#print axioms card_pic_le_324_of_stabC
#print axioms card_pic_le_324_of_body
-- witness matching
#print axioms fibre_eq
#print axioms fibre_finite_le_324
#print axioms val_fieldMap_of_rat
#print axioms exists_restrict_qbar
#print axioms galPt_mem_fibre
#print axioms matched_fibre
#print axioms DeligneCore.map
#print axioms exists_moduli_map
#print axioms exists_deligneCore
-- assembly, descent and the consumer
#print axioms exists_transfer
#print axioms exists_transfer_equiv
#print axioms t11b_proved
#print axioms DeligneCore.exists_rep_units
#print axioms exists_cmOrder_card_pic_le_324
#print axioms model_equiv
#print axioms not_rat_of_ringEquiv
#print axioms exists_suborder_card_pic_le_324
#print axioms conductor_dvd_of_le
#print axioms abs_orderDisc_le
#print axioms fowler_of_le
#print axioms faltingsHeight_le_bcm_of_sub
