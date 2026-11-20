import ZInQKernel.Contrib.OneProof.T10Proetale.AffineWeaklyEtaleLimits
import ZInQKernel.Contrib.OneProof.T10Proetale.AffineLocalLifts
import ZInQKernel.Contrib.OneProof.T10Proetale.CountableLocalLifts
import ZInQKernel.Contrib.OneProof.T10Proetale.IntegralTower

open ZInQ.Manuscript.T10Proetale

#print axioms flat_of_filteredCocones
#print axioms flat_of_affineLimits
#print axioms weaklyEtale_of_affineLimit
#print axioms surjective_of_affineLimit
#print axioms affineDiagramLimit
#print axioms affineSequenceLimitCover
#print axioms proUnderlying
#print axioms proSingletonCover
#print axioms affineCover_lift
#print axioms countable_affineCover_lifts
#print axioms proProduct_epi
#print axioms residueQuotientProduct_epi
#print axioms proFiniteH1Limit
#print axioms proReduction_existsUnique
#print axioms proReductionEquiv
#print axioms proReductionEquiv_apply

open Lean Elab Command in
run_cmd do
  let declarations : List (Name × Name) := [
    (`ZInQKernel.Contrib.OneProof.T10Proetale.AffineWeaklyEtaleLimits, `ZInQ.Manuscript.T10Proetale.lift_finite_family),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.AffineWeaklyEtaleLimits, `ZInQ.Manuscript.T10Proetale.pullbackDiagram),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.AffineWeaklyEtaleLimits, `ZInQ.Manuscript.T10Proetale.pullbackDiagramCone),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.AffineWeaklyEtaleLimits, `ZInQ.Manuscript.T10Proetale.pullbackDiagramConeIsLimit),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.AffineLocalLifts, `ZInQ.Manuscript.T10Proetale.J),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.AffineLocalLifts, `ZInQ.Manuscript.T10Proetale.over_w),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.AffineLocalLifts, `ZInQ.Manuscript.T10Proetale.pro_open_family_cover),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.AffineLocalLifts, `ZInQ.Manuscript.T10Proetale.proDisjointUnion),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.AffineLocalLifts, `ZInQ.Manuscript.T10Proetale.proDisjointUnionMap),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.AffineLocalLifts, `ZInQ.Manuscript.T10Proetale.gluing_local_lifts),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CountableLocalLifts, `ZInQ.Manuscript.T10Proetale.J),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CountableLocalLifts, `ZInQ.Manuscript.T10Proetale.ASh),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CountableLocalLifts, `ZInQ.Manuscript.T10Proetale.LiftStep),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CountableLocalLifts, `ZInQ.Manuscript.T10Proetale.chooseLiftStep),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CountableLocalLifts, `ZInQ.Manuscript.T10Proetale.liftTower),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CountableLocalLifts, `ZInQ.Manuscript.T10Proetale.liftTowerStep),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CountableLocalLifts, `ZInQ.Manuscript.T10Proetale.sectionType),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CountableLocalLifts, `ZInQ.Manuscript.T10Proetale.sectionType_preservesLimits),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.CountableLocalLifts, `ZInQ.Manuscript.T10Proetale.product_section_lifts),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.IntegralTower, `ZInQ.Manuscript.T10Proetale.reductionToLimit)
  ]
  for (moduleName, declName) in declarations do
    let name := mkPrivateNameCore moduleName declName
    elabCommand (← `(command| #print axioms $(mkIdent name)))
