import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Assembly

open Lean Elab Command

/-- Run the ordinary axiom printer on a private constant's internal name. -/
elab "#print_private_axioms " internal:str : command => do
  let name := (internal.getString.splitOn ".").foldl
    (fun name part => match part.toNat? with
      | some n => name.num n
      | none => name.str part) Name.anonymous
  let cmd ← `(#print axioms $(mkCIdent name):ident)
  elabCommand cmd

#print axioms ZInQ.Manuscript.RC.ThetaClose.exceptionalProduct_ne_zero
#print axioms ZInQ.Manuscript.RC.ThetaClose.actualPmLocal
#print axioms ZInQ.Manuscript.RC.ThetaClose.actualFilteredSupport
#print axioms ZInQ.Manuscript.RC.ThetaClose.actualLevelStage
#print axioms ZInQ.Manuscript.RC.ThetaClose.actualLevelValLift
#print axioms ZInQ.Manuscript.RC.ThetaClose.integerBasis
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.MatrixTest.0.ZInQ.Manuscript.RC.ThetaClose.integerBasis_det"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.MatrixTest.0.ZInQ.Manuscript.RC.ThetaClose.integerBasis_cast"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.MatrixTest.0.ZInQ.Manuscript.RC.ThetaClose.integerBasis_image"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.MatrixTest.0.ZInQ.Manuscript.RC.ThetaClose.ternaryMatrix"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.MatrixTest.0.ZInQ.Manuscript.RC.ThetaClose.integer_test"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.MatrixTest.0.ZInQ.Manuscript.RC.ThetaClose.basis_test"
#print axioms ZInQ.Manuscript.RC.ThetaClose.memNbr_iff_padic_basis
#print axioms ZInQ.Manuscript.RC.ThetaClose.coord_memNbr_iff
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Neighbour.0.ZInQ.Manuscript.RC.ThetaClose.conjugateChart"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Neighbour.0.ZInQ.Manuscript.RC.ThetaClose.conjugateChart_mem"
#print axioms ZInQ.Manuscript.RC.ThetaClose.transportedSplit
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Neighbour.0.ZInQ.Manuscript.RC.ThetaClose.at_step"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Neighbour.0.ZInQ.Manuscript.RC.ThetaClose.local_step_iff"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Neighbour.0.ZInQ.Manuscript.RC.ThetaClose.scale_p_away_iff"
#print axioms ZInQ.Manuscript.RC.ThetaClose.transportedNeighbourLattice
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Neighbour.0.ZInQ.Manuscript.RC.ThetaClose.chart"
#print axioms ZInQ.Manuscript.RC.ThetaClose.correction
#print axioms ZInQ.Manuscript.RC.ThetaClose.indexedStep
#print axioms ZInQ.Manuscript.RC.ThetaClose.indexedStep_class
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Neighbour.0.ZInQ.Manuscript.RC.ThetaClose.heckeBasis_norm"
#print axioms ZInQ.Manuscript.RC.ThetaClose.indexedStep_valuation
#print axioms ZInQ.Manuscript.RC.ThetaClose.alignedFrame
#print axioms ZInQ.Manuscript.RC.ThetaClose.indexedTransport
#print axioms ZInQ.Manuscript.RC.ThetaClose.DiscriminantData
#print axioms ZInQ.Manuscript.RC.ThetaClose.prime_not_dvd_of_symbol_ne_zero
#print axioms ZInQ.Manuscript.RC.ThetaClose.discriminantDisjoint
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Roots.0.ZInQ.Manuscript.RC.ThetaClose.levelCoprime"
#print axioms ZInQ.Manuscript.RC.ThetaClose.prescribedParity
#print axioms ZInQ.Manuscript.RC.ThetaClose.prescribedParity_val
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Roots.0.ZInQ.Manuscript.RC.ThetaClose.complexCharacter"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Roots.0.ZInQ.Manuscript.RC.ThetaClose.chosen"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Roots.0.ZInQ.Manuscript.RC.ThetaClose.boundPrimes"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Roots.0.ZInQ.Manuscript.RC.ThetaClose.mem_boundPrimes"
#print axioms ZInQ.Manuscript.RC.ThetaClose.complexRoots
#print axioms ZInQ.Manuscript.RC.ThetaClose.complexRoots_parity
#print axioms ZInQ.Manuscript.RC.ThetaClose.characterValues
#print axioms ZInQ.Manuscript.RC.ThetaClose.characterValues_order
#print axioms ZInQ.Manuscript.RC.ThetaClose.CharacterField
#print axioms ZInQ.Manuscript.RC.ThetaClose.characterFieldNumberField
#print axioms ZInQ.Manuscript.RC.ThetaClose.coefficientPlace
#print axioms ZInQ.Manuscript.RC.ThetaClose.coefficientPlace_over_two
#print axioms ZInQ.Manuscript.RC.ThetaClose.Coefficients
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Roots.0.ZInQ.Manuscript.RC.ThetaClose.liftCharacter"
#print axioms ZInQ.Manuscript.RC.ThetaClose.levelRoots
#print axioms ZInQ.Manuscript.RC.ThetaClose.levelRoots_parity
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Support.0.ZInQ.Manuscript.RC.ThetaClose.extend_nonzero"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Support.0.ZInQ.Manuscript.RC.ThetaClose.affine_det"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Support.0.ZInQ.Manuscript.RC.ThetaClose.positive_level_split"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Support.0.ZInQ.Manuscript.RC.ThetaClose.splitVector"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Support.0.ZInQ.Manuscript.RC.ThetaClose.affine_range"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Support.0.ZInQ.Manuscript.RC.ThetaClose.affine_det_on_sphere"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Support.0.ZInQ.Manuscript.RC.ThetaClose.levelSupport"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Support.0.ZInQ.Manuscript.RC.ThetaClose.dyadicSupport"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Support.0.ZInQ.Manuscript.RC.ThetaClose.nilSupport"
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.ThetaClose.Support.0.ZInQ.Manuscript.RC.ThetaClose.divisionSupport"
#print axioms ZInQ.Manuscript.RC.ThetaClose.FilteredSupport
#print axioms ZInQ.Manuscript.RC.ThetaClose.filteredSupport
