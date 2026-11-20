import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Complete

/-! Kernel axiom audit for the even unary stage and every auxiliary theorem. -/

open Lean in
macro "#print_private_axioms" mod:ident decl:ident : command =>
  `(#print axioms $(mkCIdent (mkPrivateNameCore mod.getId decl.getId)))

-- Assembly
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Assembly ZInQ.Manuscript.RC.EvenUnary.changeLevel_unit
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Assembly ZInQ.Manuscript.RC.EvenUnary.cusp_mul_half
#print axioms ZInQ.Manuscript.RC.EvenUnary.evenUnaryStageLaw_of_ordinaryDilation
#print axioms ZInQ.Manuscript.RC.EvenUnary.evenExpansion_of_ordinaryDilation

-- Characters
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Characters ZInQ.Manuscript.RC.EvenUnary.changeLevel_int
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Characters ZInQ.Manuscript.RC.EvenUnary.character_pow_unit
#print axioms ZInQ.Manuscript.RC.EvenUnary.sievedCharacter_odd
#print axioms ZInQ.Manuscript.RC.EvenUnary.sievedCharacter_at_unit
#print axioms ZInQ.Manuscript.RC.EvenUnary.good_factors_iff_coprime
#print axioms ZInQ.Manuscript.RC.EvenUnary.coprime_supportModulus
#print axioms ZInQ.Manuscript.RC.EvenUnary.four_mul_sq_dvd_cube
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Characters ZInQ.Manuscript.RC.EvenUnary.odd_unit
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Characters ZInQ.Manuscript.RC.EvenUnary.jacobiUnitHom_one
#print axioms ZInQ.Manuscript.RC.EvenUnary.jacobiCharacter_at_unit

-- Complete
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Complete ZInQ.Manuscript.RC.EvenUnary.theta_dilation_period
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Complete ZInQ.Manuscript.RC.EvenUnary.theta_dilation_ne
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Complete ZInQ.Manuscript.RC.EvenUnary.right_T_entries
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Complete ZInQ.Manuscript.RC.EvenUnary.ordinaryDilation_nontriangular
#print axioms ZInQ.Manuscript.RC.EvenUnary.ordinaryDilationComparison_proved
#print axioms ZInQ.Manuscript.RC.EvenUnary.evenUnaryStageLaw
#print axioms ZInQ.Manuscript.RC.EvenUnary.evenExpansion_of_unary

-- Cusps
#print axioms ZInQ.Manuscript.RC.EvenUnary.weightedTheta_holo
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Cusps ZInQ.Manuscript.RC.EvenUnary.coe_action
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Cusps ZInQ.Manuscript.RC.EvenUnary.im_neg_inv
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Cusps ZInQ.Manuscript.RC.EvenUnary.neg_inv_neg_inv
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Cusps ZInQ.Manuscript.RC.EvenUnary.norm_poisson_factor
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Cusps ZInQ.Manuscript.RC.EvenUnary.cusp_positive
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Cusps ZInQ.Manuscript.RC.EvenUnary.cusp_zero
#print axioms ZInQ.Manuscript.RC.EvenUnary.weightedTheta_cusps

-- Finite
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Finite ZInQ.Manuscript.RC.EvenUnary.phase_reduction
#print axioms ZInQ.Manuscript.RC.EvenUnary.quadratic_zero_residue
#print axioms ZInQ.Manuscript.RC.EvenUnary.weightedQuadraticFourier_even
#print axioms ZInQ.Manuscript.RC.EvenUnary.weightedQuadraticFourier_odd

-- Lines
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Lines ZInQ.Manuscript.RC.EvenUnary.jacobiDerivative_ne
#print axioms ZInQ.Manuscript.RC.EvenUnary.linearTheta_hasSum
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Lines ZInQ.Manuscript.RC.EvenUnary.jacobiDerivative_eq
#print axioms ZInQ.Manuscript.RC.EvenUnary.linearLine_hasSum
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Lines ZInQ.Manuscript.RC.EvenUnary.linearLine_eq
#print axioms ZInQ.Manuscript.RC.EvenUnary.linearLine_poisson
#print axioms ZInQ.Manuscript.RC.EvenUnary.linearTheta_periodic

-- OddDenominator
#print axioms ZInQ.Manuscript.RC.EvenUnary.ordinaryTheta_odd_denominator

-- OrdinaryPhase
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.OrdinaryPhase ZInQ.Manuscript.RC.EvenUnary.coe_action
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.OrdinaryPhase ZInQ.Manuscript.RC.EvenUnary.theta_inversion
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.OrdinaryPhase ZInQ.Manuscript.RC.EvenUnary.sqrt_mul_positive
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.OrdinaryPhase ZInQ.Manuscript.RC.EvenUnary.ratio_odd_denom
#print axioms ZInQ.Manuscript.RC.EvenUnary.ordinaryPhase_prime

-- PrimeGauss
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.PrimeGauss ZInQ.Manuscript.RC.EvenUnary.primeQuadraticFourier
#print axioms ZInQ.Manuscript.RC.EvenUnary.primeGauss_scale
#print axioms ZInQ.Manuscript.RC.EvenUnary.primeGauss_sq
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.PrimeGauss ZInQ.Manuscript.RC.EvenUnary.primeCharacter_at_int
#print axioms ZInQ.Manuscript.RC.EvenUnary.primeGauss_scale_jacobi
#print axioms ZInQ.Manuscript.RC.EvenUnary.primeGauss_sq_jacobi

-- Relative
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Relative ZInQ.Manuscript.RC.EvenUnary.coe_action
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Relative ZInQ.Manuscript.RC.EvenUnary.im_positive_mul
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Relative ZInQ.Manuscript.RC.EvenUnary.relative_pos
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Relative ZInQ.Manuscript.RC.EvenUnary.relative_zero
#print axioms ZInQ.Manuscript.RC.EvenUnary.weightedTheta_relative

-- Resum
#print axioms ZInQ.Manuscript.RC.EvenUnary.weightedTheta_hasSum
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Resum ZInQ.Manuscript.RC.EvenUnary.jacobiTerm_addChar
#print axioms ZInQ.Manuscript.RC.EvenUnary.weightedTheta_fourier
#print axioms ZInQ.Manuscript.RC.EvenUnary.weightedTheta_periodic
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Resum ZInQ.Manuscript.RC.EvenUnary.rationalArgument_im
#print axioms ZInQ.Manuscript.RC.EvenUnary.weightedTheta_rational_resum
#print axioms ZInQ.Manuscript.RC.EvenUnary.norm_linearTheta_le
#print axioms ZInQ.Manuscript.RC.EvenUnary.weightedTheta_differentiableAt

-- Shell
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Shell ZInQ.Manuscript.RC.EvenUnary.shell_term
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Shell ZInQ.Manuscript.RC.EvenUnary.shell_reindex
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Shell ZInQ.Manuscript.RC.EvenUnary.jacobiTerm_shell
#print axioms ZInQ.Manuscript.RC.EvenUnary.unaryFun_eq_weightedTheta

-- Transform
#print axioms ZInQ.Manuscript.RC.EvenUnary.weightedTheta_rational_modes
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenUnary.Transform ZInQ.Manuscript.RC.EvenUnary.tsum_even_odd
#print axioms ZInQ.Manuscript.RC.EvenUnary.weightedTheta_at_cusp
