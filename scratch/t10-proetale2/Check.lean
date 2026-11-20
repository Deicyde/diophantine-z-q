import ZInQKernel.Contrib.OneProof.T10Proetale.DiscreteCoefficients
import ZInQKernel.Contrib.OneProof.T10Proetale.LiftTorsor
import ZInQKernel.Contrib.OneProof.T10Proetale.SplitCover
import ZInQKernel.Contrib.OneProof.T10Proetale.LocalRepresentatives
import ZInQKernel.Contrib.OneProof.T10Proetale.ResidueLimit
import ZInQKernel.Contrib.OneProof.T10Proetale.CoefficientSequence
import ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts
import ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyProducts
import ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyLimit
import ZInQKernel.Contrib.OneProof.T10Proetale.GeometricSquares

open ZInQ.Manuscript.T10Proetale

-- DiscreteCoefficients
#print axioms proOpen
#print axioms proOpenInclusion
#print axioms proOpenCover
#print axioms constantToContinuous
#print axioms constantToContinuous_locallyInjective
#print axioms constantToContinuous_locallySurjective
#print axioms discreteCoefficientsIso

-- LiftTorsor
#print axioms sectionAt
#print axioms liftPresheaf
#print axioms liftPresheaf_isSheaf
#print axioms liftSheaf
#print axioms liftTrivialization
#print axioms liftTrivialization_restrict
#print axioms liftSheaf_locallyNonempty

-- SplitCover
#print axioms splitProjection
#print axioms splitProjection_surjective
#print axioms splitProjection_spec_finite
#print axioms splitProjection_spec_etale
#print axioms splitSheet
#print axioms splitLift
#print axioms splitLift_projection
#print axioms splitLift_sheet
#print axioms splitLift_unique
#print axioms splitSections
#print axioms splitSections_restrict

-- LocalRepresentatives
#print axioms localLiftSections
#print axioms localLiftSections_restrict

-- ResidueLimit
#print axioms compatibleResidues
#print axioms residueEval
#print axioms residueEval_compat
#print axioms padicOfResidues
#print axioms toResidue_padicOfResidues
#print axioms continuous_of_continuous_residues
#print axioms existsUnique_continuous_residueLift

-- CoefficientSequence
#print axioms residueSheaf
#print axioms productSheaf
#print axioms productProjection
#print axioms productFanIsLimit
#print axioms differenceHom
#print axioms differenceHom_surjective_sections
#print axioms differenceHom_epi
#print axioms integralToProduct
#print axioms coefficientSequence
#print axioms coefficientSequence_shortExact

-- ExtProducts
#print axioms extProductMap
#print axioms extProductMap_injective
#print axioms extProductMap_bijective

-- CohomologyProducts
#print axioms cohomologySource
#print axioms productH1Coordinates
#print axioms productH1Coordinates_injective
#print axioms productH1Coordinates_bijective

-- CohomologyLimit
#print axioms proReduction_injective
#print axioms proReduction_existsUnique_of_compatible

-- GeometricSquares
#print axioms geometricHom
#print axioms galAut_geometricHom
#print axioms geometricMultiplication
#print axioms galAut_geometricMultiplication

-- Check the private declarations from their defining modules as well.
open Lean Elab Command in
run_cmd do
  let declarations : List (Name × Name) := [
    (`ZInQKernel.Contrib.OneProof.T10Proetale.LiftTorsor, `ZInQ.Manuscript.T10Proetale.sectionAt_restrict),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.SplitCover, `ZInQ.Manuscript.T10Proetale.diagonalAlgebraMap),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.SplitCover, `ZInQ.Manuscript.T10Proetale.splitProjection_spec),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.SplitCover, `ZInQ.Manuscript.T10Proetale.splitSheet_ι),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.SplitCover, `ZInQ.Manuscript.T10Proetale.fibreOpen),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.SplitCover, `ZInQ.Manuscript.T10Proetale.fibreCover),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.SplitCover, `ZInQ.Manuscript.T10Proetale.fibreLift_compatible),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.SplitCover, `ZInQ.Manuscript.T10Proetale.splitLift_restrict),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.LocalRepresentatives, `ZInQ.Manuscript.T10Proetale.coefficientPresentation),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.LocalRepresentatives, `ZInQ.Manuscript.T10Proetale.quotientSections),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.LocalRepresentatives, `ZInQ.Manuscript.T10Proetale.geometricLiftSheaf),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CoefficientSequence, `ZInQ.Manuscript.T10Proetale.productLift),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CoefficientSequence, `ZInQ.Manuscript.T10Proetale.difference),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CoefficientSequence, `ZInQ.Manuscript.T10Proetale.integralToProduct_injective_sections),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CoefficientSequence, `ZInQ.Manuscript.T10Proetale.integralToProduct_zero),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CoefficientSequence, `ZInQ.Manuscript.T10Proetale.integralToProduct_lift_sections),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts, `ZInQ.Manuscript.T10Proetale.injectives),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts, `ZInQ.Manuscript.T10Proetale.quotients),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts, `ZInQ.Manuscript.T10Proetale.productPresentation),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts, `ZInQ.Manuscript.T10Proetale.productPresentation_exact_mono),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts, `ZInQ.Manuscript.T10Proetale.productPresentation_shortExact),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts, `ZInQ.Manuscript.T10Proetale.productPresentationProjection),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts, `ZInQ.Manuscript.T10Proetale.boundary_projection),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts, `ZInQ.Manuscript.T10Proetale.quotientPresentation),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts, `ZInQ.Manuscript.T10Proetale.quotientPresentation_shortExact),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts, `ZInQ.Manuscript.T10Proetale.quotientMap),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts, `ZInQ.Manuscript.T10Proetale.quotientPresentationToProduct),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts, `ZInQ.Manuscript.T10Proetale.quotient_boundary_projection),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyProducts, `ZInQ.Manuscript.T10Proetale.extFanMap),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyProducts, `ZInQ.Manuscript.T10Proetale.extFanMap_comp),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyProducts, `ZInQ.Manuscript.T10Proetale.extFanMap_injective),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyProducts, `ZInQ.Manuscript.T10Proetale.extFanMap_bijective),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyLimit, `ZInQ.Manuscript.T10Proetale.mapH_sub_apply),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyLimit, `ZInQ.Manuscript.T10Proetale.extH1_injective),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyLimit, `ZInQ.Manuscript.T10Proetale.differenceHom_project),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyLimit, `ZInQ.Manuscript.T10Proetale.productH1Coordinates_difference),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyLimit, `ZInQ.Manuscript.T10Proetale.productH1Coordinates_integral),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyLimit, `ZInQ.Manuscript.T10Proetale.differenceH0_surjective)
  ]
  for (moduleName, declName) in declarations do
    let name := mkPrivateNameCore moduleName declName
    elabCommand (← `(command| #print axioms $(mkIdent name)))
