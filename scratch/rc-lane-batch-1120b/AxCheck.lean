import ZInQKernel.Contrib.OneProof.RC.AppE32Fixed.Central
import ZInQKernel.Contrib.OneProof.RC.AppE32Fixed.Clearing
import ZInQKernel.Contrib.OneProof.RC.AppE32Fixed.Fixed
import ZInQKernel.Contrib.OneProof.RC.AppEK1.CoefficientCohomology
import ZInQKernel.Contrib.OneProof.RC.AppEK1.Coefficients
import ZInQKernel.Contrib.OneProof.RC.AppEK1.Comparison
import ZInQKernel.Contrib.OneProof.RC.AppEK1.FiniteIdentity
import ZInQKernel.Contrib.OneProof.RC.AppEK1.ShapiroTransfer
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Analytic
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Assembly
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Generic
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Sign
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Specialization
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Uniformization
import ZInQKernel.Contrib.OneProof.RC.AtkinSign.Family
import ZInQKernel.Contrib.OneProof.RC.AtkinSign.Geometry
import ZInQKernel.Contrib.OneProof.RC.CMField2.AnalyticDegree
import ZInQKernel.Contrib.OneProof.RC.CMField2.CoordinateDescent
import ZInQKernel.Contrib.OneProof.RC.CMField2.CosetLattice
import ZInQKernel.Contrib.OneProof.RC.CMField2.Cyclic
import ZInQKernel.Contrib.OneProof.RC.CMField2.Degree
import ZInQKernel.Contrib.OneProof.RC.CMField2.Descent
import ZInQKernel.Contrib.OneProof.RC.CMField2.Diagonal
import ZInQKernel.Contrib.OneProof.RC.CMField2.ExactOrder
import ZInQKernel.Contrib.OneProof.RC.CMField2.ExactOrderProof
import ZInQKernel.Contrib.OneProof.RC.CMField2.Factorization
import ZInQKernel.Contrib.OneProof.RC.CMField2.Frobenius
import ZInQKernel.Contrib.OneProof.RC.CMField2.HeegnerLattice
import ZInQKernel.Contrib.OneProof.RC.CMField2.IdealDictionary
import ZInQKernel.Contrib.OneProof.RC.CMField2.Integrality
import ZInQKernel.Contrib.OneProof.RC.CMField2.Kronecker
import ZInQKernel.Contrib.OneProof.RC.CMField2.Lattices
import ZInQKernel.Contrib.OneProof.RC.CMField2.LevelOne
import ZInQKernel.Contrib.OneProof.RC.CMField2.LevelTwo
import ZInQKernel.Contrib.OneProof.RC.CMField2.Membership
import ZInQKernel.Contrib.OneProof.RC.CMField2.MembershipDegree
import ZInQKernel.Contrib.OneProof.RC.CMField2.Multipliers
import ZInQKernel.Contrib.OneProof.RC.CMField2.NormCriterion
import ZInQKernel.Contrib.OneProof.RC.CMField2.OrderGenerator
import ZInQKernel.Contrib.OneProof.RC.CMField2.OrientedIdeals
import ZInQKernel.Contrib.OneProof.RC.CMField2.PrimeComparison
import ZInQKernel.Contrib.OneProof.RC.CMField2.PrimitiveNorms
import ZInQKernel.Contrib.OneProof.RC.CMField2.Results
import ZInQKernel.Contrib.OneProof.RC.CMField2.ScalarWitness
import ZInQKernel.Contrib.OneProof.RC.CMField2.SplitPrime
import ZInQKernel.Contrib.OneProof.RC.CalLocalLengths.Calibration
import ZInQKernel.Contrib.OneProof.RC.CalLocalLengths.LocalOrders
import ZInQKernel.Contrib.OneProof.RC.CalLocalLengths.Suppliers
import ZInQKernel.Contrib.OneProof.RC.CalPres.Actions
import ZInQKernel.Contrib.OneProof.RC.CalPres.Presentations
import ZInQKernel.Contrib.OneProof.RC.CalPres.SplitModel
import ZInQKernel.Contrib.OneProof.RC.ElkikPrint.Finiteness
import ZInQKernel.Contrib.OneProof.RC.ElkikPrint.Prints
import ZInQKernel.Contrib.OneProof.RC.ElkikPrint.Reduction
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Assembly
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Jacobi
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Mask
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.MaskCore
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Operators
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Ordinary
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Permutation
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Projector
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.SeriesBounds
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Unary
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Affine
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Assembly
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Character
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Dilation
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Matrices
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.PrimeGauss
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Theta
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Translate
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Assembly
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Characters
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Complete
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Cusps
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Finite
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Lines
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.OddDenominator
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.OrdinaryPhase
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.PrimeGauss
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Relative
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Resum
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Shell
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Transform
import ZInQKernel.Contrib.OneProof.RC.EvenUpperCubes.Application
import ZInQKernel.Contrib.OneProof.RC.EvenUpperCubes.Level
import ZInQKernel.Contrib.OneProof.RC.EvenUpperCubes.Realize
import ZInQKernel.Contrib.OneProof.RC.GoodReduction.Atkin
import ZInQKernel.Contrib.OneProof.RC.GoodReduction.Integral
import ZInQKernel.Contrib.OneProof.RC.GoodReduction.Row
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.AffineLimit
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.BaseValue
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.BranchExpansion
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ChartComparison
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.CuspAssignment
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.CuspComparison
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.CuspOrbits
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.Endpoints
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.Factor
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.FixedScaleComparison
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.FormalBranches
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.GeometricTorsion
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.LaurentLimit
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.LimitUniqueness
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ModelJacobian
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ModelSource
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.PointedCurve
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveAbelian
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectivePoints
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveUniformization
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.SourceLimit
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.TranslatedBranches
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.Triangular
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.WeierstrassPeriods
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.WeightedComparison
import ZInQKernel.Contrib.OneProof.RC.Kato812.Kato812Finite
import ZInQKernel.Contrib.OneProof.RC.Kato812.Kato812Interface
import ZInQKernel.Contrib.OneProof.RC.Kato812.Kato812Print
import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Determinant
import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Old
import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Operator
import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Packet
import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Shift
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.ActualFamily
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.At
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Character
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Family
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Filter
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Ideals
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.IdeleClass
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Join
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Norm
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Parametrization
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Schwartz
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Stage
import ZInQKernel.Contrib.OneProof.RC.O7Character.Basis
import ZInQKernel.Contrib.OneProof.RC.O7Character.Character
import ZInQKernel.Contrib.OneProof.RC.O7Character.Stage
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Assembly
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Local
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Norm
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Orientation
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Transport
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Weights
import ZInQKernel.Contrib.OneProof.RC.O7Residual.Artin
import ZInQKernel.Contrib.OneProof.RC.O7Residual.At
import ZInQKernel.Contrib.OneProof.RC.O7Residual.Family
import ZInQKernel.Contrib.OneProof.RC.O7Residual.IdealNorm
import ZInQKernel.Contrib.OneProof.RC.O7Residual.Orbit
import ZInQKernel.Contrib.OneProof.RC.O7Residual.OrbitQuotient
import ZInQKernel.Contrib.OneProof.RC.O7Residual.ReducedNorm
import ZInQKernel.Contrib.OneProof.RC.SelectorTotal.Assembly
import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Assembly
import ZInQKernel.Contrib.OneProof.RC.ThetaClose.MatrixTest
import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Neighbour
import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Roots
import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Support
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.AdelicNorm
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Assembly
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Conjugation
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Coordinates
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Frame
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Global
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Invariance
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.LevelTheta
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.LocalOrder
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Neighbour
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.NormCharacter
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Phase
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.ReducedNorm
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Schwartz
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Support
import ZInQKernel.Contrib.OneProof.RC.TorusWeights.Actual
import ZInQKernel.Contrib.OneProof.RC.TorusWeights.Norm
import ZInQKernel.Contrib.OneProof.RC.X0Model3.AffineEval
import ZInQKernel.Contrib.OneProof.RC.X0Model3.Model
import ZInQKernel.Contrib.OneProof.RC.X0Model3.Overlap
import ZInQKernel.Contrib.OneProof.RC.X0Model3.Specialize
import ZInQKernel.Contrib.OneProof.RC.X0Model3.Unramified
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.FixedScaleElkik
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveAdditionCoordinates
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveAdditionFormula
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveChartGluing
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveGroupIdentities
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveGroupLaw
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveSchemeCharts

namespace ZInQ.Manuscript.RC.AppE32Fixed
section
#print axioms central_zero_iff_of_wedge
end
end ZInQ.Manuscript.RC.AppE32Fixed
namespace ZInQ.Manuscript.RC.AppE32Fixed
section
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Determinant
#print axioms outerWitness_of_completed_coefficients
end
end ZInQ.Manuscript.RC.AppE32Fixed
namespace ZInQ.Manuscript.RC.AppE32Fixed
section
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open EvenUpperText PrintsArith Wiring
#print axioms appEOutputs_of_kato_fixed
#print axioms evenScalar32_of_kato_fixed
end
end ZInQ.Manuscript.RC.AppE32Fixed
namespace ZInQ.Manuscript.RC.AtkinPin
section
open scoped MatrixGroups ModularForm Manifold TauCeti.ExactDivisor
open Complex UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open ZInQ.Contrib.CloudB3RC53.CST
#print axioms slash_eq_signUnit_smul
#print axioms scaled_eichler_transform
#print axioms periodClass_transform
end
end ZInQ.Manuscript.RC.AtkinPin
namespace ZInQ.Manuscript.RC.AtkinPin
section
open scoped NumberField WeierstrassCurve Classical
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility
open ZInQ.Manuscript.SelmerTwoPower
open O7Actual O7Assemble O7Orbits O7Residual PMGeometry ThetaClose SelectorTotal
#print axioms consumerNewform
#print axioms stageLevel_eq
#print axioms oddStagedOfPinnedParamValues
end
end ZInQ.Manuscript.RC.AtkinPin
namespace ZInQ.Manuscript.RC.AtkinPin
section
open scoped Classical MatrixGroups TauCeti.ExactDivisor
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open PreparedParam
#print axioms atkinInterior_apply
#print axioms atkinInterior_involutive
#print axioms phiAn_transform
#print axioms projectiveValue_transform_chart
#print axioms actualParametrization_transform_chart
#print axioms translatedAtkinOnPoints
#print axioms translatedAtkinAtInfinity
end
end ZInQ.Manuscript.RC.AtkinPin
namespace ZInQ.Manuscript.RC.AtkinPin
section
open scoped TauCeti.ExactDivisor
#print axioms signUnit_cast
#print axioms wNew_cast
end
end ZInQ.Manuscript.RC.AtkinPin
namespace ZInQ.Manuscript.RC.AtkinPin
section
open scoped Classical TauCeti.ExactDivisor
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open FreeAbelianGroup (of)
open PreparedParam
open PMGeometry (DivZero center)
#print axioms atkin_quotient_of_specialization
#print axioms pinned_atkin_quotient_of_specialization
end
end ZInQ.Manuscript.RC.AtkinPin
namespace ZInQ.Manuscript.RC.AtkinPin
section
open WeierstrassCurve ZInQ.Contrib.CloudB3RC53.CST
#print axioms weierPt_add
end
end ZInQ.Manuscript.RC.AtkinPin
namespace ZInQ.Manuscript.RC.AtkinSign
section
open scoped NumberField WeierstrassCurve Classical
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility
open O7Actual O7Assemble O7Orbits O7Residual PMGeometry ThetaClose
#print axioms actualRowFamily
#print axioms oddStagedActual
end
end ZInQ.Manuscript.RC.AtkinSign
namespace ZInQ.Manuscript.RC.AtkinSign
section
open FreeAbelianGroup (of)
open PMGeometry (DivZero center)
open Stages
#print axioms SpecialFibreAtSigns
#print axioms SpecialFibreAtSigns.toSpecialFibre
#print axioms SpecialFibreAtSigns.atkinSign_eq
#print axioms SpecialFibreAtSigns.ofSpecialFibre
end
end ZInQ.Manuscript.RC.AtkinSign
namespace ZInQ.Manuscript.RC.CMField2
section
open NumberField TauCeti.GlobalNumberFields ZInQ.Contrib.CloudB3RC53.CST
open scoped UpperHalfPlane
#print axioms eq_cmPoint_of_quadratic
#print axioms singularModulus_finrank_le_of_primitive_equation
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open AlgebraicGeometry NumberField TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.PreparedParam
#print axioms cmFieldOfDefinition_modelOne_of
#print axioms heegner_coordinates_mem_ringClass_of
#print axioms branchDescends_one
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open UpperHalfPlane Polynomial ModularCurve Module Matrix
#print axioms exists_cyclic_sublattice_of_modularPolynomial_root
#print axioms exists_analyticJ_eq
#print axioms conjugate_has_cyclic_self_of_root
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open Module
#print axioms isAddCyclic_quotient_of_primitive
#print axioms isAddCyclic_sublatticeQuotient_of_primitive
#print axioms primitive_of_isAddCyclic_quotient
#print axioms primitive_of_isAddCyclic_sublatticeQuotient
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open NumberField Module IntermediateField TauCeti.GlobalNumberFields
#print axioms ConjugateSingularModulus
#print axioms finrank_adjoin_le_of_conjugate_family
#print axioms singularModulus_finrank_le_of_conjugate
#print axioms singularModulus_finrank_over_base_le_of_conjugate
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open AlgebraicGeometry CategoryTheory NumberField TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudW07JacobiansCurves
open PreparedParam
#print axioms BranchDescends
#print axioms affineEval_factor
#print axioms chart_mem
#print axioms fieldPoint_of_affineEval_range
#print axioms fieldPoint_of_finitePointEval_range
#print axioms fieldPoint_iff_finitePointEval_range
#print axioms cmFieldOfDefinition_of
#print axioms fieldPoint_of_eval_mem_adjoin_coordinates
#print axioms fieldPoint_of_eval_rational_in_coordinates
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open Polynomial ModularCurve
#print axioms eval_diagonal
#print axioms rootMultiplicity_specialization_eq_of_embeddings
#print axioms isIntegral_jLattice_of_cyclicSelf
#print axioms exists_nonsquare_quadratic_value
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open NumberField Module ModularCurve Polynomial TauCeti.GlobalNumberFields
#print axioms ExactMultiplierOrderOfDiagonalMultiplicities
#print axioms conjugateSingularModulus_of_exactMultiplier
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open NumberField Module ModularCurve Polynomial IntermediateField TauCeti.GlobalNumberFields
#print axioms periodMultipliers_idealPeriod
#print axioms exactMultiplierOrderOfDiagonalMultiplicities
#print axioms conjugateSingularModulus
#print axioms singularModulus_finrank_le
#print axioms singularModulus_finrank_over_base_le
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open Polynomial UpperHalfPlane ModularCurve Matrix
open scoped MatrixGroups
#print axioms coe_cosetParameter
#print axioms injOn_coset_j_of_transcendental
#print axioms modularPolynomial_eq_coset_product
#print axioms exists_coset_of_modularPolynomial_root
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
#print axioms pow_eq_of_kronecker_diagonal
#print axioms mem_of_separating_reductions
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open ZInQ.Contrib.CloudB3RC53.CST UpperHalfPlane Complex
open scoped Pointwise
#print axioms coe_cmPoint_of_neg
#print axioms heegner_middle_coprime
#print axioms heegner_scaled_form
#print axioms heegner_pairLattice_mul
#print axioms dilate_cmPoint_eq
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open NumberField Module TauCeti.GlobalNumberFields FractionalIdeal
open scoped nonZeroDivisors
#print axioms proper_iff_isUnit
#print axioms exists_singularModulus_of_exact_multiplier
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open NumberField Module TauCeti.GlobalNumberFields Matrix Polynomial
open scoped nonZeroDivisors
#print axioms cast_sublatticeIndex_scale
#print axioms exists_order_basis_one
#print axioms orderBasis_im_ne_zero
#print axioms singularModulus_isIntegral
#print axioms cast_absNorm_span_singleton_complex
#print axioms prime_diagonal_eq_of_order_multiplier
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open Polynomial ModularCurve
#print axioms modularPolynomial_reduced_root
#print axioms kroneckerCongruence_of_prime
#print axioms pow_eq_of_modularPolynomial_diagonal_root
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open NumberField Module TauCeti.GlobalNumberFields FractionalIdeal
open scoped nonZeroDivisors
#print axioms exists_ideal_basis
#print axioms idealPeriod
#print axioms idealPeriod_lattice
#print axioms singularModulus
#print axioms jLattice_eq_of_lattice_eq
#print axioms jLattice_scale
#print axioms lattice_scale
#print axioms singularModulus_eq_of_mkPic_eq
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open AlgebraicGeometry CategoryTheory ModularCurve NumberField
open ZInQ.Contrib.CloudW07JacobiansCurves
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.PreparedParam
#print axioms finiteChart_finiteTest
#print axioms finitePointEval_one_mem_range
#print axioms modelOne_fieldPoint_of_analyticJ
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open UpperHalfPlane Complex Matrix
open scoped MatrixGroups
open ZInQ.Contrib.CloudB3RC53.CST
#print axioms levelTwo_heegner
#print axioms levelTwo_reflection
#print axioms levelTwo_coordinates
#print axioms middleCoefficient_mod_four
#print axioms levelTwo_distinct
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open NumberField TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
#print axioms SingularModulusMemRingClass
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open NumberField Module IntermediateField TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
#print axioms singularModulus_finrank_over_base_le_of_mem
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open Module
#print axioms periodMultipliers
#print axioms exists_multiplier_basis_one
#print axioms exists_normalized_multiplier
#print axioms periodMultipliers_scale
#print axioms periodMultipliers_eq_of_jLattice_eq
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open ModularCurve Polynomial UpperHalfPlane
#print axioms diagonal_root_iff_primitive_norm
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open NumberField Module TauCeti.GlobalNumberFields Complex
open scoped nonZeroDivisors
#print axioms discr_of_basis_one
#print axioms exists_heegner_generator
#print axioms exists_heegner_generator_in_embedding
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open NumberField Module TauCeti.GlobalNumberFields FractionalIdeal
open ZInQ.Contrib.CloudB3RC53.CST
open scoped nonZeroDivisors Pointwise
#print axioms formIdeal
#print axioms formIdeal_coe
#print axioms formIdeal_restrictScalars
#print axioms formIdeal_mul_conjugate
#print axioms formIdeal_isUnit
#print axioms analyticJ_eq_singularModulus_of_generator
#print axioms formIdeal_mul_scaled
#print axioms formIdeal_scaled_eq_levelInverse_mul
#print axioms exists_heegner_singularModuli_in_embedding
#print axioms exists_heegner_singularModuli
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open NumberField Ideal Polynomial Module IntermediateField TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
#print axioms splitPrime_of_frob_fixes_ringClass
#print axioms singularModulusMemRingClass
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
#print axioms primitiveNormLevels
#print axioms quadraticNormParameters_eq_of_primitiveNormLevels
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open AlgebraicGeometry NumberField TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.PreparedParam
#print axioms cmFieldOfDefinition
#print axioms cmFieldOfDefinition_modelOne
#print axioms cmFieldOfDefinition_one
#print axioms heegner_coordinates_mem_ringClass
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open Polynomial ModularCurve
#print axioms exists_homothetic_of_jLattice_eq
#print axioms exists_int_eq_of_real_multiplier
#print axioms conjugate_has_nonreal_multiplier_of_root
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Manuscript.RC.CMField2
section
open NumberField Module TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
open Polynomial ModularCurve
#print axioms singularModulus_reduction_pow_eq_of_split
end
end ZInQ.Manuscript.RC.CMField2
namespace ZInQ.Contrib.RC53Assist.Calibration
section
open NumberField IsDedekindDomain CategoryTheory Matrix TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.CloudB3RC53.RankCounts (resAbs_apply_coe)
#print axioms centralSignedTateAction
#print axioms movingInertiaAction
#print axioms activeInertiaAction
#print axioms signedReduced_subScalar
#print axioms movingReduced_subScalar
#print axioms activeSignedTate_subOne_even
#print axioms activeReduced_apply
end
end ZInQ.Contrib.RC53Assist.Calibration
namespace ZInQ.Contrib.RC53Assist.Calibration
section
open CategoryTheory NumberField IsDedekindDomain Matrix
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
#print axioms kummerFirstCoordinate
#print axioms presentationOfSplit
#print axioms movingBlock
#print axioms movingOrdinary
#print axioms activeBlock
#print axioms movingPresentation
#print axioms activePresentation
#print axioms presentationAtZero
end
end ZInQ.Contrib.RC53Assist.Calibration
namespace ZInQ.Contrib.RC53Assist.Calibration
section
open CategoryTheory
open ZInQ.Manuscript.RC.Local
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
#print axioms splitLocalModel
#print axioms splitLocalH1
#print axioms splitLocalH2
#print axioms quotientOfFirstCoordinate
#print axioms activeMiddleCoordinates
#print axioms activeMiddleCoordinates_d0
#print axioms activeMiddleCoordinates_d1
#print axioms movingTameNormalization
#print axioms tameNorm_negId
#print axioms activeTameNormalization
end
end ZInQ.Contrib.RC53Assist.Calibration
namespace ZInQ.Manuscript.RC.ElkikPrint
section
open scoped MatrixGroups
#print axioms cuspClass_finiteRange_of_cuspOrbits
#print axioms maninDrinfeld_of_torsion
end
end ZInQ.Manuscript.RC.ElkikPrint
namespace ZInQ.Manuscript.RC.ElkikPrint
section
open scoped MatrixGroups
open HeckeRing.GL2
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
#print axioms hElkikMD_of_elkikTorsion
end
end ZInQ.Manuscript.RC.ElkikPrint
namespace ZInQ.Manuscript.RC.EvenExpansion
section
open AddressGenuine AuxInputs BlocksPerU CongruenceSubgroup EvenBudget Matrix.SpecialLinearGroup
open ModularForm O12 PrintsAnalytic ThetaCoeff UpperHalfPlane Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53
open scoped BigOperators MatrixGroups ModularForm
#print axioms moving_nil
#print axioms moving_of_step
#print axioms weightTwoBlock
#print axioms unaryLevel_dvd
#print axioms includeUnary_mem
#print axioms evenWeightTwo
#print axioms evenVector_eval
#print axioms evenExpansion
end
end ZInQ.Manuscript.RC.EvenExpansion
namespace ZInQ.Manuscript.RC.EvenExpansion
section
open Complex CongruenceSubgroup Matrix Matrix.SpecialLinearGroup ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups
#print axioms jacobiTheta_fourth_transform
end
end ZInQ.Manuscript.RC.EvenExpansion
namespace ZInQ.Manuscript.RC.EvenExpansion
section
open AddressGenuine AppE AuxInputs EvenBudget HalfIntegral PrintsAnalytic Wiring
open ZInQ.Manuscript.RC.Even
open BlocksPerU CongruenceSubgroup UpperHalfPlane Filter
open ZInQ.Contrib.CloudB3RC53
open scoped BigOperators Manifold MatrixGroups
#print axioms threeHalves_of_cusp
#print axioms hasThreeHalves_of_cusp
#print axioms evenMasked
#print axioms evenMasked_reference
#print axioms evenMasked_expansion
end
end ZInQ.Manuscript.RC.EvenExpansion
namespace ZInQ.Manuscript.RC.EvenExpansion
section
open AppE HalfIntegral PrintsAnalytic UpperHalfPlane
open scoped BigOperators Classical
#print axioms quadraticProjection
end
end ZInQ.Manuscript.RC.EvenExpansion
namespace ZInQ.Manuscript.RC.EvenExpansion
section
open UpperHalfPlane HalfIntegral Function Odd
open scoped BigOperators ZMod
#print axioms series_Vp
#print axioms series_Up
#print axioms series_Up_sq_Vp
#print axioms movingOp_series
end
end ZInQ.Manuscript.RC.EvenExpansion
namespace ZInQ.Manuscript.RC.EvenExpansion
section
open BlocksPerU Complex CongruenceSubgroup Matrix Matrix.SpecialLinearGroup ModularForm
open OldStageLaw PrintsAnalytic
open UpperHalfPlane hiding I
open scoped BigOperators MatrixGroups
#print axioms ordinaryTheta_cusps
#print axioms ordinaryTheta_fourth
#print axioms ordinaryThetaLaw
end
end ZInQ.Manuscript.RC.EvenExpansion
namespace ZInQ.Manuscript.RC.EvenExpansion
section
#print axioms upSquare_permutation
#print axioms upSquare_conjugation
end
end ZInQ.Manuscript.RC.EvenExpansion
namespace ZInQ.Manuscript.RC.EvenExpansion
section
open scoped BigOperators Classical
#print axioms dual_orthogonality
end
end ZInQ.Manuscript.RC.EvenExpansion
namespace ZInQ.Manuscript.RC.EvenExpansion
section
#print axioms summable_squareShell
end
end ZInQ.Manuscript.RC.EvenExpansion
namespace ZInQ.Manuscript.RC.EvenExpansion
section
open EvenBudget UpperHalfPlane
open scoped BigOperators Classical
#print axioms exists_unary_parity
#print axioms unary_hasSum
end
end ZInQ.Manuscript.RC.EvenExpansion
namespace ZInQ.Manuscript.RC.GoodReduction
section
open AlgebraicGeometry CategoryTheory Limits CartesianMonoidalCategory
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj
open FreeAbelianGroup (of)
open PMGeometry (DivZero center)
#print axioms atkinQuotient_of_affine
#print axioms atkinQuotient_of_integralRelation
end
end ZInQ.Manuscript.RC.GoodReduction
namespace ZInQ.Manuscript.RC.GoodReduction
section
open AlgebraicGeometry CategoryTheory Limits
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj
#print axioms existsUnique_integralMap
#print axioms exists_integralPoint
#print axioms integralAffine_baseChange
end
end ZInQ.Manuscript.RC.GoodReduction
namespace ZInQ.Manuscript.RC.GoodReduction
section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Contrib.ChebFD.C10 (GQ)
open scoped WeierstrassCurve Classical
open PreparedParam PMGeometry WitnessSpec
#print axioms hpi_of_integralDiagram
end
end ZInQ.Manuscript.RC.GoodReduction
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory Filter PkgI3
open scoped TensorProduct Topology
#print axioms maps_to_rat_unique
#print axioms sectionEval
#print axioms sectionMap_factor
#print axioms tendsto_specPoint
#print axioms tendsto_complexLift_of_sections
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory Filter ModularCurve MonObj MonoidalCategory PkgI3 UpperHalfPlane
open scoped Topology
#print axioms cusp_at_infinity_maps_to_unit
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open Filter ModularCurve ShimuraPointDict
open scoped Topology
#print axioms branch_expansion
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory Limits MonObj PkgI3 Filter UpperHalfPlane
open Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology
#print axioms complexLift_comp
#print axioms value_eq_of_chart_limit
#print axioms cuspLimit_eq_zero_of_jacobi_ne_zero
#print axioms cuspComparison_of_zero_chart_limit
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory Filter ModularCurve PkgI3 UpperHalfPlane
open Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology
#print axioms cuspIndex
#print axioms orbitOfSL
#print axioms orbitOfSL_surjective
#print axioms orbitOfSL_eq
#print axioms algebraicCusp
#print axioms extendPoint
#print axioms extendPoint_injective
#print axioms rationalAsGeometric
#print axioms algebraicCusp_limit
#print axioms algebraicCusp_zero
#print axioms algebraicCusp_infinity
#print axioms algebraicCusp_zero_rational
#print axioms algebraicCusp_infinity_rational
#print axioms cuspAssignment_zero_limit
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory Filter MonObj PkgI3 UpperHalfPlane
open Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology
#print axioms extendJacobian
#print axioms cusp_comparison_of_factor
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
#print axioms exists_gamma0_smul_zero
#print axioms cuspOrbit_eq_zero_of_coprime
#print axioms cuspOrbit_eq_zero_of_jacobi_ne_zero
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory Filter Function ModularCurve PkgI3 UpperHalfPlane
open scoped MatrixGroups Topology
#print axioms analyticJ_invariant
#print axioms tendsto_infinity
#print axioms tendsto_zero
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj PkgI3
open scoped MatrixGroups
#print axioms factor_isMonHom
#print axioms abelJacobi_comp_factor
#print axioms abelJacobi_comp_isBased
#print axioms torusHom_pointClass
#print axioms torusHom_cuspClass_of_jacobi_ne_zero
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open HeckeRing.GL2
open AlgebraicGeometry CategoryTheory Limits Filter MonObj PkgI3 UpperHalfPlane WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open scoped Topology
open PreparedParam
#print axioms hElkikMD_atScale_of_projectiveGroup
#print axioms targetPeriodEquiv
#print axioms targetPeriodEquiv_lift
#print axioms algebraicCuspClass_comparison_atScale
#print axioms hElkikMD_atScale_of_geometricTorsion
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory ModularCurve Polynomial IntermediateField
#print axioms triangularField
#print axioms triangularField_j
#print axioms triangularField_jN
#print axioms zeroField
#print axioms zeroField_j
#print axioms zeroField_jN
#print axioms formalBranch
#print axioms formalBranch_generic
#print axioms branchPoint
#print axioms zeroPoint
#print axioms zeroPoint_overQ
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open CategoryTheory MonObj PkgI3 HeckeRing.GL2
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
#print axioms geometricCuspidalSubgroup_finite
#print axioms hElkikMD_of_geometricTorsion
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open Filter
open scoped Topology
#print axioms powerSeries_analytic_sum
#print axioms tendsto_powerSeries_eval
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory Limits PkgI3
#print axioms t2_of_affine_pair
#print axioms source_t2
#print axioms source_limit_unique
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj PkgI3
#print axioms infinity
#print axioms modelCurve
#print axioms modelPicardRep
#print axioms J0
#print axioms aj0
#print axioms aj0_classifies
#print axioms isJacobian_aj0
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory ModularCurve
open ZInQ.Contrib.CloudW07JacobiansCurves ZInQ.Contrib.CurvesG
#print axioms source
#print axioms model_smooth_one
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open CategoryTheory MonoidalCategory AlgebraicGeometry
#print axioms rationalPoint
#print axioms isCurve_of_point
#print axioms pointedSourceCurve
#print axioms basedJacobian
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj PkgI3 WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme
#print axioms projectiveAbVar
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj WeierstrassCurve HomogeneousLocalization Filter PkgI3
open scoped Topology
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open PreparedParam
#print axioms weierstrassOrigin
#print axioms weierstrassOrigin_point
#print axioms projectiveValue_eq_zero_iff
#print axioms projectiveValue_bijective
#print axioms projectiveGroup_origin
#print axioms projectiveValue_vector_affine
#print axioms projectiveValue_vector_origin
#print axioms tendsto_projectiveVectorPoint
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory Filter Limits PkgI3 WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.RC53Assist.IsogenyScheme
open scoped Topology PeriodPair
open PreparedParam
#print axioms projectiveTorusValue_lift
#print axioms projectiveTorusValue_lift_of_eval
#print axioms projectivePeriodHomeomorph
#print axioms continuous_projectiveTorusValue
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory Filter ModularCurve ShimuraPointDict PkgI3
open scoped Topology
#print axioms interior
#print axioms branchComplex
#print axioms sourceLimit_of_generator_expansions
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory Filter Function Matrix ModularCurve PkgI3 UpperHalfPlane
open scoped MatrixGroups Topology
#print axioms Qbar
#print axioms qbarToComplex
#print axioms exists_algebraic_cusp_limit
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open Matrix
open scoped MatrixGroups
#print axioms exists_primitive_triangular
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open WeierstrassCurve ZInQ.Contrib.CloudB3RC53.CST
#print axioms weierstrassCoordinates_nonsingular
#print axioms weierstrassPeriodEquiv
#print axioms weierstrassPeriodEquiv_mk
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory Filter MonObj PkgI3 UpperHalfPlane
open Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology
#print axioms algebraicCuspClass
#print axioms algebraicCuspClass_factors
#print axioms modularFactor
#print axioms modularFactor_isMonHom
#print axioms aj0_comp_modularFactor
#print axioms cusp_comparison
#print axioms weighted_comparison
#print axioms weighted_comparison_from_limits
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.TorusWeights
section
open scoped Quaternion NumberField nonZeroDivisors
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open Eichler Visibility Visibility.ThetaStage O7Actual
#print axioms NormFactors.rightProduct
#print axioms SchwartzFactors.eval_order
#print axioms sign_square
#print axioms frame_transport
#print axioms torus_character
#print axioms orbit_transport
#print axioms actualWeights
#print axioms datumWeights
end
end ZInQ.Manuscript.RC.TorusWeights
namespace ZInQ.Manuscript.RC.TorusWeights
section
open scoped Quaternion NumberField
open NumberField IsDedekindDomain
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open Eichler O7Actual
#print axioms localNrd
#print axioms NormFactors.onIntegralNorm
#print axioms descent_of_filter
end
end ZInQ.Manuscript.RC.TorusWeights
namespace ZInQ.Manuscript.RC.X0Model3
section
open AlgebraicGeometry CategoryTheory Filter ModularCurve ShimuraPointDict
open ZInQ.Contrib.CloudW07JacobiansCurves
open scoped Topology
#print axioms affineEval
#print axioms affineEval_congr
#print axioms affineEval_injective
#print axioms finiteChart
#print axioms eventually_chart_mem
#print axioms chartEval
#print axioms chartEval_center
#print axioms chartEval_at_mem
#print axioms chartEval_analyticAt
#print axioms finitePointEval
#print axioms finitePointEval_eq
#print axioms exists_analyticJN_ratio
end
end ZInQ.Manuscript.RC.X0Model3
namespace ZInQ.Manuscript.RC.X0Model3
section
open AlgebraicGeometry Filter ModularCurve
open scoped Topology MatrixGroups
open X0Model2
#print axioms exists_stabilizer_germ_match
#print axioms complexPoint_eq_iff
#print axioms model
end
end ZInQ.Manuscript.RC.X0Model3
namespace ZInQ.Manuscript.RC.X0Model3
section
open AlgebraicGeometry CategoryTheory Filter ModularCurve
open ZInQ.Contrib.CloudW07JacobiansCurves ZInQ.Contrib.CurvesG
open scoped Topology MatrixGroups
#print axioms eventually_overlap_of_complexPoint_eq
end
end ZInQ.Manuscript.RC.X0Model3
namespace ZInQ.Manuscript.RC.X0Model3
section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Contrib.ChebFD.C10 (GQ)
open scoped WeierstrassCurve Classical
open PreparedParam PMGeometry WitnessSpec
#print axioms projectiveValue_eq_of_complexPoint
#print axioms datumReduction_projectiveValue
#print axioms hpi_iff_specialize_projectiveValue
#print axioms specialize_of_integral_extension
end
end ZInQ.Manuscript.RC.X0Model3
namespace ZInQ.Manuscript.RC.X0Model3
section
open Algebra Filter Topology
open scoped TensorProduct
#print axioms eventually_eq_of_unramified
end
end ZInQ.Manuscript.RC.X0Model3
namespace ZInQ.Manuscript.RC.J0Cusps
section
open scoped Classical
open HeckeRing.GL2
open AlgebraicGeometry CategoryTheory MonObj PkgI3 WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
#print axioms hElkikMD_atScale
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open scoped Classical
open WeierstrassCurve
open scoped WeierstrassCurve.Projective
#print axioms nonsingular_of_equation_ne_zero
#print axioms additionCoordinates_fields
#print axioms additionCoordinates_map
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open WeierstrassCurve
open scoped WeierstrassCurve.Projective
#print axioms symmetricAddition_map
#print axioms symmetricAddition_smul
#print axioms symmetricAddition_eq_smul_add
#print axioms projectiveNonsingular_ne_zero
#print axioms projectiveAddition_cover
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open PreparedParam
#print axioms schemeMapsToRat_unique
#print axioms projectiveMorphism_of_local
#print axioms projectiveMorphism_of_formulas
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open scoped Classical
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory PkgI3
open WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open PreparedParam
#print axioms projectiveUnit_value
#print axioms projectiveHom_ext
#print axioms projectiveTarget_square_reduced
#print axioms projectiveGroupOfOperations
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open scoped Classical
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj PkgI3
open WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open PreparedParam
#print axioms exists_projectiveMultiplication
#print axioms exists_projectiveInversion
#print axioms projectiveGroup_exists
end
end ZInQ.Manuscript.RC.J0Cusps
namespace ZInQ.Manuscript.RC.J0Cusps
section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme
#print axioms projectiveChartRatio_self
#print axioms projectiveChart_dehomogenize
#print axioms projectiveChart_equation
#print axioms projectiveChart_ringHom_ext
#print axioms projectiveChartEval_ratio
#print axioms projectiveChartMorphism_map
#print axioms projectiveChartMorphism_independent
#print axioms projectiveValue_chartMorphism
#print axioms projectiveValue_fromChart
end
end ZInQ.Manuscript.RC.J0Cusps
