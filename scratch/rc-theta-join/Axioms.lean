import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Phase
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Global
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.LocalOrder
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Schwartz
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Frame
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.ReducedNorm
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.NormCharacter
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.AdelicNorm
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Invariance
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Conjugation
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Neighbour
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Coordinates
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Assembly
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.LevelTheta
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Support

open Lean Elab Command

/-- Run the ordinary axiom printer on a private constant's internal name. -/
elab "#print_private_axioms " internal:str : command => do
  let name := (internal.getString.splitOn ".").foldl
    (fun name part => match part.toNat? with
      | some n => name.num n
      | none => name.str part) Name.anonymous
  let cmd ← `(#print axioms $(mkCIdent name):ident)
  elabCommand cmd

#print axioms ZInQ.Manuscript.RC.ThetaJoin.PhaseData.mem_support
#print axioms ZInQ.Manuscript.RC.ThetaJoin.PhaseData.natUnit_val
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Phase.0.ZInQ.Manuscript.RC.ThetaJoin.PhaseData.away_mul"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Phase.0.ZInQ.Manuscript.RC.ThetaJoin.PhaseData.away_one"
#print axioms ZInQ.Manuscript.RC.ThetaJoin.PhaseData.away_of_not_mem
#print axioms ZInQ.Manuscript.RC.ThetaJoin.PhaseData.scalar_mul
#print axioms ZInQ.Manuscript.RC.ThetaJoin.PhaseData.scalar_order
#print axioms ZInQ.Manuscript.RC.ThetaJoin.PhaseData.phase_good
#print axioms ZInQ.Manuscript.RC.ThetaJoin.PhaseData.phase_unit
#print axioms ZInQ.Manuscript.RC.ThetaJoin.PhaseData.phase_order
#print axioms ZInQ.Manuscript.RC.ThetaJoin.PhaseData.eta_one
#print axioms ZInQ.Manuscript.RC.ThetaJoin.PhaseData.eta_mul
#print axioms ZInQ.Manuscript.RC.ThetaJoin.PhaseData.eta_good
#print axioms ZInQ.Manuscript.RC.ThetaJoin.PhaseData.scalarSign_sq
#print axioms ZInQ.Manuscript.RC.ThetaJoin.PhaseData.unaryParity_odd
#print axioms ZInQ.Manuscript.RC.ThetaJoin.weightAt_of_local
#print axioms ZInQ.Manuscript.RC.ThetaJoin.latticeSphere_finite
#print axioms ZInQ.Manuscript.RC.ThetaJoin.weight_finiteSupp
#print axioms ZInQ.Manuscript.RC.ThetaJoin.weightAt_zero
#print axioms ZInQ.Manuscript.RC.ThetaJoin.coefficientAt_zero
#print axioms ZInQ.Manuscript.RC.ThetaJoin.atRep_left
#print axioms ZInQ.Manuscript.RC.ThetaJoin.weightAt_left
#print axioms ZInQ.Manuscript.RC.ThetaJoin.coefficientAt_left
#print axioms ZInQ.Manuscript.RC.ThetaJoin.localUnit_conj_mem
#print axioms ZInQ.Manuscript.RC.ThetaJoin.atRep_right
#print axioms ZInQ.Manuscript.RC.ThetaJoin.weightAt_right
#print axioms ZInQ.Manuscript.RC.ThetaJoin.atRep_nsmul
#print axioms ZInQ.Manuscript.RC.ThetaJoin.localUnit_smul_cancel
#print axioms ZInQ.Manuscript.RC.ThetaJoin.weightAt_scale
#print axioms ZInQ.Manuscript.RC.ThetaJoin.weightedAt_change
#print axioms ZInQ.Manuscript.RC.ThetaJoin.weightedCoefficient_eq
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.LocalOrder.0.ZInQ.Manuscript.RC.ThetaJoin.matrix_mul_complement"
#print axioms ZInQ.Manuscript.RC.ThetaJoin.split_invariants
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.LocalOrder.0.ZInQ.Manuscript.RC.ThetaJoin.integralMatrix_injective"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.LocalOrder.0.ZInQ.Manuscript.RC.ThetaJoin.split_image"
#print axioms ZInQ.Manuscript.RC.ThetaJoin.splitOrderEquiv_apply
#print axioms ZInQ.Manuscript.RC.ThetaJoin.divisionCompletion
#print axioms ZInQ.Manuscript.RC.ThetaJoin.splitIdentification
#print axioms ZInQ.Manuscript.RC.ThetaJoin.divisionIdentification
#print axioms ZInQ.Manuscript.RC.ThetaJoin.mem_exceptionalPlaces
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Schwartz.0.ZInQ.Manuscript.RC.ThetaJoin.levelExponent_pos"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Schwartz.0.ZInQ.Manuscript.RC.ThetaJoin.legendre_two_power"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Schwartz.0.ZInQ.Manuscript.RC.ThetaJoin.re_unit_smul_iff"
#print axioms ZInQ.Manuscript.RC.ThetaJoin.divisionFactor_zero
#print axioms ZInQ.Manuscript.RC.ThetaJoin.splitFactor_scale
#print axioms ZInQ.Manuscript.RC.ThetaJoin.divisionFactor_scale
#print axioms ZInQ.Manuscript.RC.ThetaJoin.localFactor_scale
#print axioms ZInQ.Manuscript.RC.ThetaJoin.schwartz_finiteSupp
#print axioms ZInQ.Manuscript.RC.ThetaJoin.schwartz_zero
#print axioms ZInQ.Manuscript.RC.ThetaJoin.schwartz
#print axioms ZInQ.Manuscript.RC.ThetaJoin.nrd_nsmul
#print axioms ZInQ.Manuscript.RC.ThetaJoin.mem_vectors
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Frame.0.ZInQ.Manuscript.RC.ThetaJoin.FrameCoordinates.residueRep_cast"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Frame.0.ZInQ.Manuscript.RC.ThetaJoin.FrameCoordinates.det_equation"
#print axioms ZInQ.Manuscript.RC.ThetaJoin.FrameCoordinates.coord_det
#print axioms ZInQ.Manuscript.RC.ThetaJoin.FrameCoordinates.coord_scale
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Frame.0.ZInQ.Manuscript.RC.ThetaJoin.FrameCoordinates.dvd_entry"
#print axioms ZInQ.Manuscript.RC.ThetaJoin.FrameCoordinates.div_vector
#print axioms ZInQ.Manuscript.RC.ThetaJoin.FrameCoordinates.coefficientAt_eq_vectors
#print axioms ZInQ.Manuscript.RC.ThetaJoin.FrameCoordinates.frame_theta
#print axioms ZInQ.Manuscript.RC.ThetaJoin.FrameCoordinates.frame_scale
#print axioms ZInQ.Manuscript.RC.ThetaJoin.FrameCoordinates.frame
#print axioms ZInQ.Manuscript.RC.ThetaJoin.norm_toLocal
#print axioms ZInQ.Manuscript.RC.ThetaJoin.norm_atRep
#print axioms ZInQ.Manuscript.RC.ThetaJoin.completion_norm_integral
#print axioms ZInQ.Manuscript.RC.ThetaJoin.val_rationalPrime
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.NormCharacter.0.ZInQ.Manuscript.RC.ThetaJoin.rationalPart_support"
#print axioms ZInQ.Manuscript.RC.ThetaJoin.rationalPart_pos
#print axioms ZInQ.Manuscript.RC.ThetaJoin.rationalPart_valuation
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.NormCharacter.0.ZInQ.Manuscript.RC.ThetaJoin.normalized_valuation"
#print axioms ZInQ.Manuscript.RC.ThetaJoin.integralUnit_val
#print axioms ZInQ.Manuscript.RC.ThetaJoin.localUnitPart_val
#print axioms ZInQ.Manuscript.RC.ThetaJoin.rationalPart_of_units
#print axioms ZInQ.Manuscript.RC.ThetaJoin.positive_rational_unit
#print axioms ZInQ.Manuscript.RC.ThetaJoin.rationalPart_diagonal
#print axioms ZInQ.Manuscript.RC.ThetaJoin.discriminantCharacter_diagonal
#print axioms ZInQ.Manuscript.RC.ThetaJoin.val_localNorm_of_orderUnit
#print axioms ZInQ.Manuscript.RC.ThetaJoin.normUnit_val
#print axioms ZInQ.Manuscript.RC.ThetaJoin.normCharacter_integral
#print axioms ZInQ.Manuscript.RC.ThetaJoin.normCharacter_diagonal
#print axioms ZInQ.Manuscript.RC.ThetaJoin.normCharacter
#print axioms ZInQ.Manuscript.RC.ThetaJoin.weight_conj
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Conjugation.0.ZInQ.Manuscript.RC.ThetaJoin.re_conj"
#print axioms ZInQ.Manuscript.RC.ThetaJoin.splitUnit_ambient
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Conjugation.0.ZInQ.Manuscript.RC.ThetaJoin.dyadic_conj_of_zero"
#print axioms ZInQ.Manuscript.RC.ThetaJoin.splitFactor_conj
#print axioms ZInQ.Manuscript.RC.ThetaJoin.divisionFactor_conj
#print axioms ZInQ.Manuscript.RC.ThetaJoin.atRep_single_away
#print axioms ZInQ.Manuscript.RC.ThetaJoin.weightAt_neighbour_scale
#print axioms ZInQ.Manuscript.RC.ThetaJoin.FrameCoordinates.frame_neighbour
#print axioms ZInQ.Manuscript.RC.ThetaJoin.atRep_re
#print axioms ZInQ.Manuscript.RC.ThetaJoin.atRep_rat_smul
#print axioms ZInQ.Manuscript.RC.ThetaJoin.GoodCoordinates.embed_matrix
#print axioms ZInQ.Manuscript.RC.ThetaJoin.GoodCoordinates.cast_matrix
#print axioms ZInQ.Manuscript.RC.ThetaJoin.GoodCoordinates.divisible
#print axioms ZInQ.Manuscript.RC.ThetaJoin.lattice_norm_integral
#print axioms ZInQ.Manuscript.RC.ThetaJoin.good_not_dvd
#print axioms ZInQ.Manuscript.RC.ThetaJoin.good_away
#print axioms ZInQ.Manuscript.RC.ThetaJoin.good_not_two
#print axioms ZInQ.Manuscript.RC.ThetaJoin.good_not_dvd_m
#print axioms ZInQ.Manuscript.RC.ThetaJoin.level_neg
#print axioms ZInQ.Manuscript.RC.ThetaJoin.weightedNeighbour_of_transport
#print axioms ZInQ.Manuscript.RC.ThetaJoin.pmLocal
#print axioms ZInQ.Manuscript.RC.ThetaJoin.actualStage
#print axioms ZInQ.Manuscript.RC.ThetaJoin.actualValLift
#print axioms ZInQ.Manuscript.RC.ThetaJoin.splitUnit_norm
#print axioms ZInQ.Manuscript.RC.ThetaJoin.levelNormCharacter_single
#print axioms ZInQ.Manuscript.RC.ThetaJoin.levelNormCharacter
#print axioms ZInQ.Manuscript.RC.ThetaJoin.levelNormCovariance
#print axioms ZInQ.Manuscript.RC.ThetaJoin.levelFrameCoordinates
#print axioms ZInQ.Manuscript.RC.ThetaJoin.levelPmLocal
#print axioms ZInQ.Manuscript.RC.ThetaJoin.levelStage
#print axioms ZInQ.Manuscript.RC.ThetaJoin.levelValLift
#print axioms ZInQ.Manuscript.RC.ThetaJoin.halfIntegral_iff
#print axioms ZInQ.Manuscript.RC.ThetaJoin.halfIntegral_iff_local
#print axioms ZInQ.Manuscript.RC.ThetaJoin.weightAt_support_iff_affine
#print axioms ZInQ.Manuscript.RC.ThetaJoin.atRep_affine_twice
#print axioms ZInQ.Manuscript.RC.ThetaJoin.affine_mem_at_odd
#print axioms ZInQ.Manuscript.RC.ThetaJoin.weight_support_iff_halfIntegral
#print axioms ZInQ.Manuscript.RC.ThetaJoin.RequestedSupport
#print axioms ZInQ.Manuscript.RC.ThetaJoin.FilteredSupport
