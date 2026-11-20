import ZInQKernel.Contrib.OneProof.RC.CMField2.AnalyticDegree
import ZInQKernel.Contrib.OneProof.RC.CMField2.LevelTwo
import ZInQKernel.Contrib.OneProof.RC.CMField2.MembershipDegree
import ZInQKernel.Contrib.OneProof.RC.CMField2.Results

/-! Checked statements for the public CMField2 results. -/

open ZInQ.Manuscript.RC.CMField2

-- Cyclic.lean
#check isAddCyclic_quotient_of_primitive
#check isAddCyclic_sublatticeQuotient_of_primitive
#check primitive_of_isAddCyclic_quotient
#check primitive_of_isAddCyclic_sublatticeQuotient

-- Diagonal.lean
#check eval_diagonal
#check isIntegral_jLattice_of_cyclicSelf
#check exists_nonsquare_quadratic_value
#check rootMultiplicity_specialization_eq_of_embeddings

-- Factorization.lean
#check coe_cosetParameter
#check injOn_coset_j_of_transcendental
#check modularPolynomial_eq_coset_product
#check exists_coset_of_modularPolynomial_root

-- Frobenius.lean
#check pow_eq_of_kronecker_diagonal
#check mem_of_separating_reductions

-- HeegnerLattice.lean
#check coe_cmPoint_of_neg
#check heegner_middle_coprime
#check heegner_scaled_form
#check heegner_pairLattice_mul
#check dilate_cmPoint_eq

-- Lattices.lean
#check exists_ideal_basis
#check idealPeriod_lattice
#check jLattice_eq_of_lattice_eq
#check jLattice_scale
#check lattice_scale
#check singularModulus_eq_of_mkPic_eq

-- PrimitiveNorms.lean
#check quadraticNormParameters_eq_of_primitiveNormLevels

-- CosetLattice.lean
#check exists_cyclic_sublattice_of_modularPolynomial_root
#check exists_analyticJ_eq
#check conjugate_has_cyclic_self_of_root

-- Integrality.lean
#check cast_sublatticeIndex_scale
#check exists_order_basis_one
#check orderBasis_im_ne_zero
#check singularModulus_isIntegral
#check cast_absNorm_span_singleton_complex
#check prime_diagonal_eq_of_order_multiplier

-- Kronecker.lean
#check modularPolynomial_reduced_root
#check kroneckerCongruence_of_prime
#check pow_eq_of_modularPolynomial_diagonal_root

-- LevelTwo.lean
#check levelTwo_heegner
#check levelTwo_reflection
#check levelTwo_coordinates
#check middleCoefficient_mod_four
#check levelTwo_distinct

-- Membership.lean
#check SingularModulusMemRingClass

-- Degree.lean
#check finrank_adjoin_le_of_conjugate_family
#check singularModulus_finrank_le_of_conjugate
#check singularModulus_finrank_over_base_le_of_conjugate
#check ConjugateSingularModulus

-- Descent.lean
#check affineEval_factor
#check fieldPoint_of_affineEval_range
#check chart_mem
#check fieldPoint_of_finitePointEval_range
#check fieldPoint_iff_finitePointEval_range
#check cmFieldOfDefinition_of
#check fieldPoint_of_eval_mem_adjoin_coordinates
#check fieldPoint_of_eval_rational_in_coordinates
#check BranchDescends

-- IdealDictionary.lean
#check proper_iff_isUnit
#check exists_singularModulus_of_exact_multiplier

-- MembershipDegree.lean
#check singularModulus_finrank_over_base_le_of_mem

-- OrderGenerator.lean
#check discr_of_basis_one
#check exists_heegner_generator
#check exists_heegner_generator_in_embedding

-- ScalarWitness.lean
#check exists_homothetic_of_jLattice_eq
#check exists_int_eq_of_real_multiplier
#check conjugate_has_nonreal_multiplier_of_root

-- SplitPrime.lean
#check singularModulus_reduction_pow_eq_of_split

-- ExactOrder.lean
#check conjugateSingularModulus_of_exactMultiplier
#check ExactMultiplierOrderOfDiagonalMultiplicities

-- LevelOne.lean
#check finiteChart_finiteTest
#check finitePointEval_one_mem_range
#check modelOne_fieldPoint_of_analyticJ

-- Multipliers.lean
#check exists_multiplier_basis_one
#check exists_normalized_multiplier
#check periodMultipliers_scale
#check periodMultipliers_eq_of_jLattice_eq

-- OrientedIdeals.lean
#check formIdeal_coe
#check formIdeal_restrictScalars
#check formIdeal_mul_conjugate
#check formIdeal_isUnit
#check analyticJ_eq_singularModulus_of_generator
#check formIdeal_mul_scaled
#check formIdeal_scaled_eq_levelInverse_mul
#check exists_heegner_singularModuli_in_embedding
#check exists_heegner_singularModuli

-- PrimeComparison.lean
#check splitPrime_of_frob_fixes_ringClass
#check singularModulusMemRingClass

-- CoordinateDescent.lean
#check branchDescends_one
#check cmFieldOfDefinition_modelOne_of
#check heegner_coordinates_mem_ringClass_of

-- NormCriterion.lean
#check diagonal_root_iff_primitive_norm

-- ExactOrderProof.lean
#check periodMultipliers_idealPeriod
#check exactMultiplierOrderOfDiagonalMultiplicities
#check conjugateSingularModulus
#check singularModulus_finrank_le
#check singularModulus_finrank_over_base_le

-- Results.lean
#check cmFieldOfDefinition
#check cmFieldOfDefinition_modelOne
#check cmFieldOfDefinition_one
#check heegner_coordinates_mem_ringClass

-- AnalyticDegree.lean
#check eq_cmPoint_of_quadratic
#check singularModulus_finrank_le_of_primitive_equation

#print ConjugateSingularModulus
#print ExactMultiplierOrderOfDiagonalMultiplicities
#print SingularModulusMemRingClass
#print BranchDescends
