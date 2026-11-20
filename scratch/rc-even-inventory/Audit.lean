import ZInQKernel.Contrib.OneProof.RC.EvenJoin.CuspidalInventory
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.EisensteinCoefficients
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ConstituentCompletion
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.BlockDescent
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ScopedBlockMatch
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.MovingCuspidal
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.UnaryCuspidal
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ActualBlocks
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ActualInventory
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ModelColumns

open Lean in
macro "#print_private_axioms" mod:ident decl:ident : command =>
  `(#print axioms $(mkCIdent (mkPrivateNameCore mod.getId decl.getId)))

#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspOldColumn.coeff_form
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspOldColumn.numberField
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspOldColumn.coeff_mem_field
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspOldColumn.char_mem_field
#print axioms ZInQ.Manuscript.RC.EvenJoin.cusp_mem_span_intrinsic
#print axioms ZInQ.Manuscript.RC.EvenJoin.finite_cuspidal_columns

#print axioms ZInQ.Manuscript.RC.EvenJoin.exists_eisenstein_coefficient_field

#print axioms ZInQ.Manuscript.RC.EvenJoin.exists_constituent_place
#print axioms ZInQ.Manuscript.RC.EvenJoin.constituent_completion_finite
#print axioms ZInQ.Manuscript.RC.EvenJoin.constituentValuation_extends
#print axioms ZInQ.Manuscript.RC.EvenJoin.constituentValuation_complete
#print axioms ZInQ.Manuscript.RC.EvenJoin.constituentValuation_integral
#print axioms ZInQ.Manuscript.RC.EvenJoin.constituentValuation_maximal
#print axioms ZInQ.Manuscript.RC.EvenJoin.constituentComplexEmbedding_constituent
#print axioms ZInQ.Manuscript.RC.EvenJoin.constituentComplexEmbedding_fixed
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.ConstituentCompletion ZInQ.Manuscript.RC.EvenJoin.constituentLocalDegree_pos
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.ConstituentCompletion ZInQ.Manuscript.RC.EvenJoin.constituentValuation_equiv
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.ConstituentCompletion ZInQ.Manuscript.RC.EvenJoin.numberField_mk_le
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.ConstituentCompletion ZInQ.Manuscript.RC.EvenJoin.mk_constituentCompletion_le

#print axioms ZInQ.Manuscript.RC.EvenJoin.coordinates_of_block_span
#print axioms ZInQ.Manuscript.RC.EvenJoin.joined_coordinates_of_block_spans

#print axioms ZInQ.Manuscript.RC.EvenJoin.joined_vector_coeff_fixedRing
#print axioms ZInQ.Manuscript.RC.EvenJoin.coordinate_match_of_joined_vector

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.MovingCuspidal ZInQ.Manuscript.RC.EvenJoin.affine_det
#print axioms ZInQ.Manuscript.RC.EvenJoin.affinePoint_zeroAtCusps
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.MovingCuspidal ZInQ.Manuscript.RC.EvenJoin.up_zeroAtCusps
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.MovingCuspidal ZInQ.Manuscript.RC.EvenJoin.sub_smul_zeroAtCusps
#print axioms ZInQ.Manuscript.RC.EvenJoin.movingOp_zeroAtCusps
#print axioms ZInQ.Manuscript.RC.EvenJoin.exists_cuspidal_moving_series

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.UnaryCuspidal ZInQ.Manuscript.RC.EvenJoin.linearTheta_norm_le_decay
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.UnaryCuspidal ZInQ.Manuscript.RC.EvenJoin.linearTheta_tendsto_zero
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.UnaryCuspidal ZInQ.Manuscript.RC.EvenJoin.coe_action
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.UnaryCuspidal ZInQ.Manuscript.RC.EvenJoin.im_neg_inv
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.UnaryCuspidal ZInQ.Manuscript.RC.EvenJoin.neg_inv_neg_inv
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.UnaryCuspidal ZInQ.Manuscript.RC.EvenJoin.norm_poisson_factor
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.UnaryCuspidal ZInQ.Manuscript.RC.EvenJoin.cusp_positive_zero
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.UnaryCuspidal ZInQ.Manuscript.RC.EvenJoin.cusp_denominator_zero
#print axioms ZInQ.Manuscript.RC.EvenJoin.weightedTheta_zeroAtCusps

#print axioms ZInQ.Manuscript.RC.EvenJoin.theta_product_cuspidal
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.ActualBlocks ZInQ.Manuscript.RC.EvenJoin.weightTwoBlock_cuspidal
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.ActualBlocks ZInQ.Manuscript.RC.EvenJoin.unaryFun_zeroAtCusps
#print axioms ZInQ.Manuscript.RC.EvenJoin.actual_cuspidal_blocks

#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspBlockExpansion.col_numberField
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspBlockExpansion.col_coeff_mem
#print axioms ZInQ.Manuscript.RC.EvenJoin.exists_actual_cuspidal_inventory
#print axioms ZInQ.Manuscript.RC.EvenJoin.actual_inventory_at_fixed_place

#print axioms ZInQ.Manuscript.RC.EvenJoin.block_span_of_inventory_labels
