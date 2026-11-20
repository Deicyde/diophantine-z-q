import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Based
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Consumer
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Coordinates
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Density
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Difference
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.FunctionField
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Infinity
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Matrix
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Model
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.PointReading
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Reduction
import ZInQKernel.Contrib.OneProof.RC.PMQuotient.Assembly
import ZInQKernel.Contrib.OneProof.RC.PMQuotient.CM
import ZInQKernel.Contrib.OneProof.RC.PMQuotient.Cusps
import ZInQKernel.Contrib.OneProof.RC.PMQuotient.Model
import ZInQKernel.Contrib.OneProof.RC.PMQuotient.Operators
import ZInQKernel.Contrib.OneProof.RC.PMWire.Assembly
import ZInQKernel.Contrib.OneProof.RC.PMWire.CM
import ZInQKernel.Contrib.OneProof.RC.PMWire.Cusps
import ZInQKernel.Contrib.OneProof.RC.PMWire.Fibre
import ZInQKernel.Contrib.OneProof.RC.PMWire.Generic
import ZInQKernel.Contrib.OneProof.RC.PMWire.Model
import ZInQKernel.Contrib.OneProof.RC.PMWire.MovingCusp
import ZInQKernel.Contrib.OneProof.RC.PMWire.Operators

namespace ZInQ.Manuscript.RC.AtkinRational
section
open scoped Classical MatrixGroups TauCeti.ExactDivisor
open AlgebraicGeometry CategoryTheory UpperHalfPlane WeierstrassCurve ModularCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.AtkinPin
#print axioms RepresentsDifference
#print axioms based_of_representedDifference
end
end ZInQ.Manuscript.RC.AtkinRational
namespace ZInQ.Manuscript.RC.AtkinRational
section
open AlgebraicGeometry CategoryTheory Limits UpperHalfPlane WeierstrassCurve CartesianMonoidalCategory
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open scoped Classical MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj TauCeti.ExactDivisor
open ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.AtkinPin
#print axioms overRelation_of_dominantPoint
#print axioms overRelationAtScale
#print axioms overRelation_baseChange
end
end ZInQ.Manuscript.RC.AtkinRational
namespace ZInQ.Manuscript.RC.AtkinRational
section
open Filter Function UpperHalfPlane ModularCurve Polynomial Matrix
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups
open ZInQ.Manuscript.RC.ModFnField
open ZInQ.Manuscript.RC.ModFnClassify
#print axioms jqN_mem_of_dvd
end
end ZInQ.Manuscript.RC.AtkinRational
namespace ZInQ.Manuscript.RC.AtkinRational
section
open AlgebraicGeometry CategoryTheory Filter UpperHalfPlane
open scoped Topology
open ZInQ.Manuscript.RC.ModFnField
#print axioms eq_constant_of_chart
end
end ZInQ.Manuscript.RC.AtkinRational
namespace ZInQ.Manuscript.RC.AtkinRational
section
open scoped Classical MatrixGroups TauCeti.ExactDivisor
open AlgebraicGeometry CategoryTheory Limits UpperHalfPlane WeierstrassCurve ModularCurve IsLocalRing
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Contrib.RC53Assist.AbelianCurve ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.AtkinPin ZInQ.Manuscript.RC.ParamAtScale
#print axioms representsDifference_of_origin
#print axioms basedAtkinAtScale
#print axioms genericFibreAtScale
end
end ZInQ.Manuscript.RC.AtkinRational
namespace ZInQ.Manuscript.RC.AtkinRational
section
open Filter Function UpperHalfPlane ModularCurve ShimuraPointDict
open scoped Topology MatrixGroups TauCeti.ExactDivisor
open ZInQ.Manuscript.RC.AtkinPin ZInQ.Manuscript.RC.ModFnClassify
open ZInQ.Manuscript.RC.X0Model
#print axioms fieldGerm_jqN
#print axioms mobius
#print axioms mobius_tendsto
#print axioms pullPuncturedGerm
#print axioms pullGerm
#print axioms pullback
#print axioms fieldGerm_pullback
end
end ZInQ.Manuscript.RC.AtkinRational
namespace ZInQ.Manuscript.RC.AtkinRational
section
open AlgebraicGeometry CategoryTheory UpperHalfPlane WeierstrassCurve ModularCurve
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.AtkinPin
open ZInQ.Manuscript.RC.ModFnField ZInQ.Manuscript.RC.ParamAtScale
#print axioms infinity_zero_of_pole
#print axioms algebraicParametrizationAtScale_atInfinity
end
end ZInQ.Manuscript.RC.AtkinRational
namespace ZInQ.Manuscript.RC.AtkinRational
section
open Filter Function UpperHalfPlane ModularCurve Polynomial Matrix
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TauCeti.ExactDivisor
open ZInQ.Manuscript.RC.AtkinPin ZInQ.Manuscript.RC.ModFnField
open ZInQ.Manuscript.RC.ModFnClassify
#print axioms chart_coordinates
end
end ZInQ.Manuscript.RC.AtkinRational
namespace ZInQ.Manuscript.RC.AtkinRational
section
open AlgebraicGeometry CategoryTheory Limits Filter UpperHalfPlane ShimuraPointDict
open scoped Topology MatrixGroups TauCeti.ExactDivisor
open ZInQ.Contrib.CloudW07JacobiansCurves ZInQ.Contrib.RC53Assist.AbelianCurve
open ZInQ.Manuscript.RC.AtkinPin ZInQ.Manuscript.RC.X0Model
open ZInQ.Manuscript.RC.ModFnClassify
open ModularCurve (modularFunctionField)
#print axioms exists_modelMap
#print axioms modelMap_chart
#print axioms exists_dominant_chart
#print axioms ext_model_of_chart
#print axioms rationalAtkin
end
end ZInQ.Manuscript.RC.AtkinRational
namespace ZInQ.Manuscript.RC.AtkinRational
section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam
#print axioms ellipticAffineOpen
#print axioms ellipticAffineIso
#print axioms ellipticAffineInclusion
#print axioms range_ellipticAffineInclusion
#print axioms mem_ellipticAffineOpen_iff
#print axioms ellipticAffineLift
#print axioms ellipticAffineLift_fac
#print axioms affineRingMap
#print axioms affineRingMap_Spec
#print axioms affineRingMap_injective
#print axioms projectiveValue_eq_some_of_affine
#print axioms projectiveValue_affine_spec
#print axioms projectiveValue_eq_zero_iff
#print axioms projectiveValue_eq_of_affine
#print axioms projectiveValue_injective_of_origin
#print axioms projectiveValue_surjective_of_origin
end
end ZInQ.Manuscript.RC.AtkinRational
namespace ZInQ.Manuscript.RC.AtkinRational
section
open scoped Classical
open AlgebraicGeometry CategoryTheory WeierstrassCurve IsLocalRing
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam
#print axioms spec_to_rat
#print axioms projectiveOverQ_proper
#print axioms projectiveReduction
#print axioms projectiveValue_specialization
end
end ZInQ.Manuscript.RC.AtkinRational
namespace ZInQ.Manuscript.RC.PMQuotient
section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open scoped NumberField WeierstrassCurve Classical
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility
open PreparedParam O7Actual O7Assemble O7Orbits O7Residual PMGeometry ThetaClose
#print axioms hCuspAt
#print axioms hpiAt
#print axioms referenceComparisons
#print axioms oddStagedOfGoodRows
end
end ZInQ.Manuscript.RC.PMQuotient
namespace ZInQ.Manuscript.RC.PMQuotient
section
open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Contrib.ChebFD.C10 (GQ)
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj WeierstrassCurve Classical
open GoodReduction (generic)
open PreparedParam PMGeometry WitnessSpec Stages
#print axioms genericInclusion_comp
#print axioms GoodRow.rawSection_over
#print axioms GoodRow.rawSection_map
#print axioms GoodRow.sectionOf_rawSection
#print axioms GoodRow.readRaw_eq
#print axioms GoodRow.readRaw_value
#print axioms cmGeneric_dominant
#print axioms hpi_of_cmDiagram
end
end ZInQ.Manuscript.RC.PMQuotient
namespace ZInQ.Manuscript.RC.PMQuotient.GoodRow
section
open AlgebraicGeometry CategoryTheory WeierstrassCurve CartesianMonoidalCategory
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj WeierstrassCurve
open GoodReduction (generic)
#print axioms hCusp
end
end ZInQ.Manuscript.RC.PMQuotient.GoodRow
namespace ZInQ.Manuscript.RC.PMQuotient
section
open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve CartesianMonoidalCategory
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj WeierstrassCurve
open FreeAbelianGroup (of)
open GoodReduction (generic)
open PMGeometry (DivZero center)
open Stages
#print axioms residueFrob
#print axioms GoodRow.hInt
#print axioms GoodRow.evaluate_frob
#print axioms GoodRow.quotient_center
#print axioms GoodRow.frobenius_quotient
end
end ZInQ.Manuscript.RC.PMQuotient
namespace ZInQ.Manuscript.RC.PMQuotient.GoodRow
section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open CartesianMonoidalCategory
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj WeierstrassCurve
open FreeAbelianGroup (of)
open GoodReduction (generic)
open PMGeometry (DivZero center)
#print axioms readAt
#print axioms value_infinity
#print axioms atkin_quotient
#print axioms hecke_quotient
#print axioms specialFibre
#print axioms specialize_eq_value
end
end ZInQ.Manuscript.RC.PMQuotient.GoodRow
namespace ZInQ.Manuscript.RC.PMWire
section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open scoped NumberField WeierstrassCurve Classical
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility
open PreparedParam O7Actual O7Assemble O7Orbits O7Residual PMGeometry ThetaClose
#print axioms transportNewform
#print axioms hCuspAt
#print axioms hpiAt
#print axioms referenceComparisons
#print axioms oddStagedOfGoodRows
end
end ZInQ.Manuscript.RC.PMWire
namespace ZInQ.Manuscript.RC.PMWire
section
open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Contrib.ChebFD.C10 (GQ)
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj WeierstrassCurve Classical
open GoodReduction (generic)
open PreparedParam PMGeometry WitnessSpec Stages
open PMQuotient (residueSource genericInclusion cmRing cmGeneric cmResidue cmGeneric_dominant)
#print axioms GoodRow.rawSection
#print axioms GoodRow.rawSection_over
#print axioms GoodRow.rawSection_map
#print axioms GoodRow.sectionOf
#print axioms GoodRow.sectionOf_rawSection
#print axioms GoodRow.readRaw
#print axioms GoodRow.readRaw_eq
#print axioms GoodRow.readRaw_value
#print axioms fixedMap
#print axioms genericProjection_comp
#print axioms hpi_of_cmDiagram
end
end ZInQ.Manuscript.RC.PMWire
namespace ZInQ.Manuscript.RC.PMWire.GoodRow
section
open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory Limits PkgI3 WeierstrassCurve
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj
open GoodReduction (generic)
open PMQuotient (residueUnit)
open PreparedParam
#print axioms based
#print axioms cuspPhi
#print axioms geometricValue
#print axioms geometricValue_injective
#print axioms translation_torsion
#print axioms KillsTranslation
#print axioms translation_killed
end
end ZInQ.Manuscript.RC.PMWire.GoodRow
namespace ZInQ.Manuscript.RC.PMWire
section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open FreeAbelianGroup (of lift)
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open scoped WeierstrassCurve
open PMGeometry (DivZero center)
open PMAdelic Stages
#print axioms embedDivisor
#print axioms adapter
#print axioms ssEquiv
#print axioms adaptComparison
#print axioms GoodRow.extendedValue
#print axioms GoodRow.quotient
#print axioms GoodRow.quotient_center
#print axioms GoodRow.quotient_center_apply
#print axioms GoodRow.extend_embed
#print axioms GoodRow.eval_hecke
#print axioms GoodRow.specialFibre
#print axioms GoodRow.specialize_eq_value
#print axioms GoodRow.cusp_eq_translation
end
end ZInQ.Manuscript.RC.PMWire
namespace ZInQ.Manuscript.RC.PMWire
section
open AlgebraicGeometry CategoryTheory Limits
open ModularCurve (modularFunctionField jq jqN jq_mem jqN_mem)
open scoped TauCeti.ExactDivisor
open GoodReduction (generic)
open ZInQ.Contrib.RC53Assist.AbelianCurve
#print axioms GenericSource.pullbackField
#print axioms GenericSource.pullback_generators
#print axioms GenericSource.exists_compactIso
#print axioms GenericSource.compactIso
#print axioms GenericSource.compactIso_generic
#print axioms GenericSource.jX
#print axioms GenericSource.jX_open
#print axioms GenericSource.jX_dominant
#print axioms integralEnd_ext
#print axioms rationalW
#print axioms ExtendsAtkin
#print axioms extendsAtkin_unique
end
end ZInQ.Manuscript.RC.PMWire
namespace ZInQ.Manuscript.RC.PMWire.GoodRow
section
open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve CartesianMonoidalCategory PkgI3
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj WeierstrassCurve
open GoodReduction (generic)
open PMQuotient (residueSource residueFrob residueUnit)
open PreparedParam Stages
#print axioms abVar
#print axioms W
#print axioms W_generic
#print axioms φ
#print axioms πInt
#print axioms hInt
#print axioms hInt_target
#print axioms readAt
#print axioms evaluate
#print axioms evaluate_frob
#print axioms value
#print axioms value_frob
#print axioms translationQ
#print axioms translationInt
#print axioms translationInt_generic
#print axioms translation
end
end ZInQ.Manuscript.RC.PMWire.GoodRow
namespace ZInQ.Manuscript.RC.PMWire
section
open AlgebraicGeometry CategoryTheory Filter ModularCurve PkgI3 UpperHalfPlane Matrix
open Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology TauCeti.ExactDivisor
open J0Cusps
open AtkinPin (atkinGL)
#print axioms MovingCusps
#print axioms movingCusps
end
end ZInQ.Manuscript.RC.PMWire
namespace ZInQ.Manuscript.RC.PMWire.GoodRow
section
open AlgebraicGeometry CategoryTheory WeierstrassCurve CartesianMonoidalCategory Limits
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj TauCeti.ExactDivisor
open FreeAbelianGroup (of)
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open GoodReduction (generic)
open PMQuotient (residueSource residueUnit)
open PreparedParam
#print axioms rationalAffine
#print axioms integralAffine
#print axioms atkin_value
#print axioms HeckeIdentity
#print axioms hecke_values
end
end ZInQ.Manuscript.RC.PMWire.GoodRow
