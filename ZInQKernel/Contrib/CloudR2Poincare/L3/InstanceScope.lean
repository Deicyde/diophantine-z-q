import Mathlib

/-!
# Explicit LOCAL activation of the owned proof-instance inventory

Names and priorities below were read from the compiler's real instance registry
in h72-L3-kernel-instance-inventory-0003. This command activates existing proof
constants only as LOCAL instances. It creates no mathematical declaration,
changes no proof type, installs no Fact, and never registers a global instance.
It is called explicitly inside owned proof scopes, not by importing this file.
-/

open Lean Elab Command

namespace ZInQ.Contrib.CloudR2Poincare.L3.InstanceScope

private def inventory : List (String × Nat) := [
  ("StacksPort.AlgebraicGeometry.SheafOfModules.isRightAdjoint_pushforward_inverseImageRingHom",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits",1000),
  ("StacksPort.Stacks.Sheaves.RingedSpaceDifferentials.modulePushforward_preservesZeroMorphisms",1000),
  ("StacksPort.Stacks.SheafOfModules.Tensor.ringSheafSectionModule",1000),
  ("StacksPort.Algebra.IsSeparableExtension.isSeparablyGenerated",1000),
  ("StacksPort.InverseImageModules.isLocallyInjective_toInverseImageRing",1000),
  ("StacksPort.Stacks.SheafOfModules.Tensor.ringSheafPresheafSymmetricCategory",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.preservesColimit_comp_stalkFunctor_forget",1000),
  ("isQuasicoherent_specField",1000),
  ("StacksPort.SemilinearStalk.isIso_stalkMap",1000),
  ("instIsClosedImmersionLeftSchemeKerι",1000),
  ("StacksPort.Stacks.Sheafify.ModuleStalkTensor.tensorAbModule",1000),
  ("StacksPort.Stacks.SheafOfModules.Tensor.ringSheafPresheafTensorRightPreservesColimits",1000),
  ("StacksPort.Stacks.Topology.CategoryStalk.openNhds_op_isFiltered",1000),
  ("StacksPort.Stacks.Sheafify.ModuleStalkTensor.tensorSheafStalkModule",1000),
  ("StacksPort.Stacks.FiniteLocallyFree.isLocallyFreeData_localGeneratorsDataOfIsIso",1000),
  ("StacksPort.RingedSpaceModuleAdjunction.modulePushforward_additive",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.toSheaf_preservesColimits",1000),
  ("StacksPort.Stacks.PresheafOfModules.Pullback.pbInstMod",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.instPreservesFiniteColimitsToTopSheaf",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.toSheaf_preservesLimits",1000),
  ("StacksPort.AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.instPreservesFiniteLimitsToTopSheaf",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.derivationAddCommGroup",1000),
  ("StacksPort.Stacks.SheafOfModules.Tensor.ringSheafSectionCommRing",1000),
  ("isMonHom_kerι",1000),
  ("StacksPort.Stacks.Sheaves.RingedSpaceDifferentials.triangleDifferentials_epi",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.derivationsFunctor_isCorepresentable_topCat",1000),
  ("instIsClosedImmersionLeftSchemeOneOverSpecOf_zInQKernel",1000),
  ("StacksPort.LocallyFreeRank.instFaithful",1000),
  ("instIsClosedImmersionLeftSchemeJK",1000),
  ("StacksPort.LocallyFreeRank.instModuleStalkPresheafCoprod",1000),
  ("StacksPort.Stacks.SheafOfModules.Tensor.ringSheafPresheafTensorLeftPreservesColimits",1000),
  ("instCompactSpaceCarrierCarrierCommRingCatLeftSchemeKerOver",1000),
  ("StacksPort.PullbackStalkTensor.instRingHomInvPairToTypeCommRingCatRingHomCarrierStalkObjFunctorOppositeOpensCarrierIsSheafGrothendieckTopologyCoeContinuousMapHomTopCatInvRingStalkRingHomStalkRingHomSymm",1000),
  ("StacksPort.AlgebraicGeometry.Scheme.Modules.moduleStalk",1000),
  ("StacksPort.InverseImageModules.isLocallyInjective_toInverseImageAb",1000),
  ("StacksPort.ChainComplex.epi_f_zero_of_quasiIso",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules",100),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.isRightAdjoint_presheafPushforward_inverseImageRingHom",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.instFaithfulToTopSheaf",1000),
  ("StacksPort.OXModule.instIsLocallySurjectiveOpensCarrierCarrierCommRingCatGrothendieckTopologyAbAddMonoidHomCarrierSheafifyUnitPshMap",1000),
  ("StacksPort.OXModule.monoidalPresheafModules",1000),
  ("StacksPort.CategoryTheory.ShortComplex.Horseshoe._sizeOf_inst",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.derivationAddCommGroupSheaf",1000),
  ("StacksPort.Stacks.SheafOfModules.Tensor.ringSheafSectionModuleOfCommRing",1000),
  ("StacksPort.InverseImageModules.isLocallySurjective_toInverseImageRing",1000),
  ("StacksPort.Stacks.Smooth.isCentralScalarMulOpposite",1000),
  ("StacksPort.OXModule.instIsLocallyInjectiveOpensCarrierCarrierCommRingCatAbAddMonoidHomCarrierGrothendieckTopologySheafifyUnitPshMap",1000),
  ("StacksPort.LocallyFreeRank.instContinuous",1000),
  ("StacksPort.Stacks.FiniteLocallyFree.isFiniteType_localGeneratorsDataOfIsIso",1000),
  ("instIsNoetherianLeftSchemeKerOver",1000),
  ("StacksPort.PullbackStalkTensor.instRingHomInvPairToTypeCommRingCatRingHomCarrierStalkObjFunctorOppositeOpensCarrierIsSheafGrothendieckTopologyInvRingCoeContinuousMapHomTopCatStalkRingHomSymmStalkRingHom",1000),
  ("instMonoOverSchemeSpecOfKerι",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.instAdditiveToTopSheaf",1000),
  ("StacksPort.LocallyFreeRank.instModuleStalkUnit",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.moduleStalkModuleOfDifferentials",1000),
  ("StacksPort.LocallyFreeRank.instFull",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits",1000),
  ("kerGrp",1000),
  ("StacksPort.Stacks.StalkFreeBridge.isLocallyFreeData_dropEmpty",1000),
  ("StacksPort.Algebra.TensorProduct.connectedSpace_primeSpectrum",1000),
  ("subsingleton_unit_left",1000),
  ("StacksPort.RingedSpaceModuleAdjunction.opensMap_isContinuous",1000),
  ("StacksPort.RingedSpaceModuleAdjunction.pushforward_structureSheafHom_isRightAdjoint",1000),
  ("StacksPort.LocallyFreeRank.instModuleStalkFree",1000),
  ("StacksPort.SemilinearStalk.isIso_ringStalkMap",1000),
  ("StacksPort.AlgebraicGeometry.instIsFilteredFExt",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules",1000),
  ("StacksPort.InverseImageModules.isLocallySurjective_toInverseImageAb",1000),
  ("instMonoOverSchemeSpecOfJK",1000),
  ("instIsLocallyNoetherianLeftSchemeKerOver",1000),
  ("StacksPort.LocallyFreeRank.instModuleStalkRestrictMod",1000),
  ("StacksPort.LocallyFreeRank.Trivialization._sizeOf_inst",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.instIsLocallyFreeOfIsFiniteLocallyFree",1000),
  ("StacksPort.Stacks.RelativeDifferentialStalk.moduleStalkRelativeDifferentials",1000),
  ("StacksPort.Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory",1000),
  ("StacksPort.Stacks.RelativeDifferentialStalk.moduleStalkSectionwiseDifferentialsSheaf",1000),
  ("instConnectedSpaceCarrierCarrierCommRingCatLeftSchemeCovOver",1000),
  ("StacksPort.AlgebraicGeometry.SheafOfModules.derivationsFunctor_isCorepresentable",1000),
  ("StacksPort.RingedSpaceModuleAdjunction.modulePullback_additive",1000),
  ("StacksPort.Stacks.StalkFreeBridge.preservesColimitsOfSize_overEquivFunctor",1000),
  ("StacksPort.CategoryTheory.Functor.quasiIso_mapAugmentation",1000),
  ("StacksPort.LocallyFreeRank.instModuleStalkF",1000),
  ("StacksPort.ClosedFibre.instIsLocalRing",1000),
  ("instIsProperHomSchemeKerOver",1000),
  ("StacksPort.CategoryTheory.ShortComplex.ownedAdditiveLeftDerived",1000)]

syntax (name := cloudR2LocalInstances) "#cloudR2LocalInstances" : command

@[command_elab cloudR2LocalInstances]
def elabLocalInstances : CommandElab := fun _ => do
  for (suffix, priority) in inventory do
    let name := suffix.splitOn "." |>.foldl Name.str `ZInQ.Contrib.CloudR2Poincare.L3
    let env ← getEnv
    if env.contains name && !Lean.Meta.isInstanceCore env name then
      liftTermElabM do Lean.Meta.addInstance name .local priority

end ZInQ.Contrib.CloudR2Poincare.L3.InstanceScope
