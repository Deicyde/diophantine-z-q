import ZInQKernel.Contrib.OneProof.RC.EvenJoin.DistinctCuspColumns
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ExactInventory
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedInventory
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.AttachmentCoefficients
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedSeed
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedFreshCoefficients
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDiamond
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.OneSeedLattice
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.OneSeedTwoFresh
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.OneSeedModel
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedTrace
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDeterminant
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedModel
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.CuspidalLocal
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedBudget

open Lean in
macro "#print_private_axioms" mod:ident decl:ident : command =>
  `(#print axioms $(mkCIdent (mkPrivateNameCore mod.getId decl.getId)))

#print axioms ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.coeff
#print axioms ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.char
#print axioms ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.field
#print axioms ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.coeff_zero
#print axioms ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.coeff_mem_field
#print axioms ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.char_mem_field
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspDilation.source_dvd
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspDilation.char
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspDilation.coeff
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspDilation.old
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspDilation.form
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspDilation.coeff_form
#print axioms ZInQ.Manuscript.RC.EvenJoin.OldNewIndependenceWeightTwo
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspDilation_coeff_independent
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspBlockExpansion.liftColumn
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspBlockExpansion.liftColumn_level
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspBlockExpansion.liftColumn_char
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspBlockExpansion.liftColumn_coeff
#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspBlockExpansion.liftColumn_field
#print axioms ZInQ.Manuscript.RC.EvenJoin.distinctCuspColumns
#print axioms ZInQ.Manuscript.RC.EvenJoin.mem_distinctCuspColumns
#print axioms ZInQ.Manuscript.RC.EvenJoin.distinctCuspIndex

#print axioms ZInQ.Manuscript.RC.EvenJoin.charAt
#print axioms ZInQ.Manuscript.RC.EvenJoin.charAt_apply
#print axioms ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.eigen
#print axioms ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.eigen_a
#print axioms ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.eigen_char
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspSources
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspOrigin
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspSource_dvd
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspSource_exists
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspSourceCoeff
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspSourceChar
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspInventory
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspInventory_coeff
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspInventory_char

#print axioms ZInQ.Manuscript.RC.EvenJoin.liftedBlockChar
#print axioms ZInQ.Manuscript.RC.EvenJoin.exists_placedCuspLists
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.κ
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.in_image
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.inventory
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.blockChar
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.blockChar_complex
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.block_span

#print axioms ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.attachment_field

#print axioms ZInQ.Manuscript.RC.EvenJoin.evenBlockLevel_dvd
#print axioms ZInQ.Manuscript.RC.EvenJoin.movingLevel_ne
#print axioms ZInQ.Manuscript.RC.EvenJoin.movingLevel_test_coprime
#print axioms ZInQ.Manuscript.RC.EvenJoin.blockSeriesAt
#print axioms ZInQ.Manuscript.RC.EvenJoin.timesTheta_map_ringHom
#print axioms ZInQ.Manuscript.RC.EvenJoin.unaryCoeff_map_ringHom
#print axioms ZInQ.Manuscript.RC.EvenJoin.TL_map_scaled
#print axioms ZInQ.Manuscript.RC.EvenJoin.blockSeriesAt_map
#print axioms ZInQ.Manuscript.RC.EvenJoin.exists_actual_placed_lists
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.fieldMap
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.ringMap
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.fieldMap_complex
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.fieldMap_source
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.evenBasis
#print axioms ZInQ.Manuscript.RC.EvenJoin.exists_placed_block_vectors
#print axioms ZInQ.Manuscript.RC.EvenJoin.placedEvenVector
#print axioms ZInQ.Manuscript.RC.EvenJoin.placed_evenVector_eval
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.phaseAt
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.rawSource
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.phase_complex
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.rawSource_complex
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.vectors
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.vectors_spec
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.seed
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.seed_support
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.seed_complex
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.ringMap_agrees
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.seed_integral

#print axioms ZInQ.Manuscript.RC.EvenJoin.fixedH_two_fresh

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDiamond ZInQ.Manuscript.RC.EvenJoin.repr
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDiamond ZInQ.Manuscript.RC.EvenJoin.blockChar_on_representative
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDiamond ZInQ.Manuscript.RC.EvenJoin.quadValue
#print axioms ZInQ.Manuscript.RC.EvenJoin.even_blockChar_sign
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDiamond ZInQ.Manuscript.RC.EvenJoin.phase_ring
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDiamond ZInQ.Manuscript.RC.EvenJoin.block_scalars
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDiamond ZInQ.Manuscript.RC.EvenJoin.scaled_shell
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDiamond ZInQ.Manuscript.RC.EvenJoin.unary_integral
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDiamond ZInQ.Manuscript.RC.EvenJoin.diamond_seed_vector
#print axioms ZInQ.Manuscript.RC.EvenJoin.placed_diamond_eval

#print axioms ZInQ.Manuscript.RC.EvenJoin.oneSeed
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneSeed_same
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneSeed_other
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneLattice
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneLatSeed
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneLatSeed_val
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneSeed_integral
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneOps
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneCoeff
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneCoeff_hecke
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneLattice_stable
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneSeed_trace_inertia

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.OneSeedTwoFresh ZInQ.Manuscript.RC.EvenJoin.dense_pair_avoid
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneSeed_twoTrace

#print axioms ZInQ.Manuscript.RC.EvenJoin.oneSeedModel
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneSeedModel_column
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneSeedModel_seed
#print axioms ZInQ.Manuscript.RC.EvenJoin.oneSeedModel_hecke

#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.sourceAttachments
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.evenAttachment
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.integral_diamonds
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.unary_inertia
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.lattice_seed_coeff
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.fresh_coeff_mem

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDeterminant ZInQ.Manuscript.RC.EvenJoin.scalar_residue
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDeterminant ZInQ.Manuscript.RC.EvenJoin.odd_residue
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.determinantData

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedModel ZInQ.Manuscript.RC.EvenJoin.fixedRing_continuousSMul
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedModel ZInQ.Manuscript.RC.EvenJoin.two_mem_extended
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedModel ZInQ.Manuscript.RC.EvenJoin.maximal_closed
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.model
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.extension
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.model_base
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.model_source
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.model_maximal
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.model_hecke
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.model_coordinates

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.CuspidalLocal ZInQ.Manuscript.RC.EvenJoin.emptySector
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.CuspidalLocal ZInQ.Manuscript.RC.EvenJoin.emptySector_shift
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspidalStage

#print axioms ZInQ.Manuscript.RC.EvenJoin.CuspidalLocalAt
#print axioms ZInQ.Manuscript.RC.EvenJoin.localAt_of_cuspidal
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedGaloisInput
#print axioms ZInQ.Manuscript.RC.EvenJoin.budgetRealization_of_placed
#print axioms ZInQ.Manuscript.RC.EvenJoin.rules_and_seed_of_placed_joint
