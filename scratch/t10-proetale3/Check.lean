import ZInQKernel.Contrib.OneProof.T10Proetale.AffineWeaklyEtaleLimits
import ZInQKernel.Contrib.OneProof.T10Proetale.AffineLocalLifts
import ZInQKernel.Contrib.OneProof.T10Proetale.CountableLocalLifts
import ZInQKernel.Contrib.OneProof.T10Proetale.IntegralTower
import ZInQKernel.Contrib.OneProof.T10Proetale.MapDescentDatum
import ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent
import ZInQKernel.Contrib.OneProof.T10Proetale.EtaleDiscreteCoefficients

open ZInQ.Manuscript.T10Proetale

#print axioms flat_of_filteredCocones
#print axioms flat_of_affineLimits
#print axioms weaklyEtale_of_affineLimit
#print axioms surjective_of_affineLimit
#print axioms affineDiagramLimit
#print axioms affineSequenceLimitCover
#print axioms proUnderlying
#print axioms proSingletonCover
#print axioms affineCover_lift_of_compactSpace
#print axioms affineCover_lift
#print axioms countable_affineCover_lifts
#print axioms proProduct_epi
#print axioms residueQuotientProduct_epi
#print axioms proFiniteH1Limit
#print axioms proReduction_existsUnique
#print axioms proReductionEquiv
#print axioms proReductionEquiv_apply
#print axioms mapDescentDatum
#print axioms mapDescentDatum_transport_image
#print axioms splitProjection_etale
#print axioms splitProjection_finite
#print axioms liftSheafRepresentableOnSlice
#print axioms liftSheaf_affineCover
#print axioms liftSheafDescentDatum
#print axioms liftSheaf_finiteEtaleDescent
#print axioms liftSheaf_finiteEtaleRepresentable
#print axioms liftSheaf_globalRepresentable
#print axioms proFiniteH1_representable
#print axioms liftSheaf_selfPullbackSplits
#print axioms etaleContinuousCoefficients
#print axioms etaleDiscreteCoefficientsIso
#print axioms etaleDiscreteCoefficientsRestrictionIso
#print axioms mapEtaleContinuousCoefficients
#print axioms etaleDiscreteCoefficientsIso_naturality
#print axioms etaleDiscreteCoefficientsRestrictionIso_naturality

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
    (`ZInQKernel.Contrib.OneProof.T10Proetale.IntegralTower, `ZInQ.Manuscript.T10Proetale.reductionToLimit),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.MapDescentDatum, `ZInQ.Manuscript.T10Proetale.mappedSquare),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.MapDescentDatum, `ZInQ.Manuscript.T10Proetale.transportCondition),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.MapDescentDatum, `ZInQ.Manuscript.T10Proetale.transition),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.MapDescentDatum, `ZInQ.Manuscript.T10Proetale.transition_congr),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.MapDescentDatum, `ZInQ.Manuscript.T10Proetale.transition_over),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.MapDescentDatum, `ZInQ.Manuscript.T10Proetale.transition_over_condition),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.MapDescentDatum, `ZInQ.Manuscript.T10Proetale.transition_comp),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.MapDescentDatum, `ZInQ.Manuscript.T10Proetale.transition_image),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.MapDescentDatum, `ZInQ.Manuscript.T10Proetale.transition_self),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.MapDescentDatum, `ZInQ.Manuscript.T10Proetale.transition_image_trans),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.MapDescentDatum, `ZInQ.Manuscript.T10Proetale.transition_trans),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent, `ZInQ.Manuscript.T10Proetale.coeffPresentation),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent, `ZInQ.Manuscript.T10Proetale.quotientSections),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent, `ZInQ.Manuscript.T10Proetale.liftPsh),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent, `ZInQ.Manuscript.T10Proetale.splitSite),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent, `ZInQ.Manuscript.T10Proetale.splitSiteMap),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent, `ZInQ.Manuscript.T10Proetale.splitSliceHomEquiv),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent, `ZInQ.Manuscript.T10Proetale.localLiftSections_congr),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent, `ZInQ.Manuscript.T10Proetale.affineOverSeparated),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent, `ZInQ.Manuscript.T10Proetale.isInvariant_preimage),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent, `ZInQ.Manuscript.T10Proetale.isEffective_of_affineMap),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent, `ZInQ.Manuscript.T10Proetale.proPullbackCover),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent, `ZInQ.Manuscript.T10Proetale.liftCover_epi),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.FiniteTorsorDescent, `ZInQ.Manuscript.T10Proetale.pullbackSliceHomEquivOfTerminal),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.EtaleDiscreteCoefficients, `ZInQ.Manuscript.T10Proetale.J),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.EtaleDiscreteCoefficients, `ZInQ.Manuscript.T10Proetale.constValue),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.EtaleDiscreteCoefficients, `ZInQ.Manuscript.T10Proetale.constantSection),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.EtaleDiscreteCoefficients, `ZInQ.Manuscript.T10Proetale.etale_openCover),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.EtaleDiscreteCoefficients, `ZInQ.Manuscript.T10Proetale.constantSection_locallyInjective),
    (`ZInQKernel.Contrib.OneProof.T10Proetale.EtaleDiscreteCoefficients, `ZInQ.Manuscript.T10Proetale.constantSection_locallySurjective)
  ]
  for (moduleName, declName) in declarations do
    let name := mkPrivateNameCore moduleName declName
    elabCommand (← `(command| #print axioms $(mkIdent name)))
open CategoryTheory AlgebraicGeometry in
example {K : Type} [Field K] (A : PkgI3.AbVar K) :
    CompactSpace (T10Etale.AKbar A) := by
  let B := A.baseChange (AlgebraicClosure K)
  have : IsProper B.X.hom := B.proper
  have : UniversallyClosed B.X.hom := B.proper.toUniversallyClosed
  have hqc : QuasiCompact B.X.hom :=
    ⟨fun _ _ h => (Scheme.Hom.isProperMap B.X.hom).isCompact_preimage h⟩
  exact @QuasiCompact.compactSpace_of_compactSpace _ _ B.X.hom hqc inferInstance

open CategoryTheory AlgebraicGeometry in
example {K : Type} [Field K] (A : PkgI3.AbVar K) :
    IsSeparated (A.baseChange (AlgebraicClosure K)).X.hom :=
  inferInstance
