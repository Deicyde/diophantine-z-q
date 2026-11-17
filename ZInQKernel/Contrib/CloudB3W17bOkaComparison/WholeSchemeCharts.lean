import ZInQKernel.Contrib.CloudB3W17bOkaComparison.ActualChartInverse
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AnalyticOpenImageIso
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.NativeLocalAnalyticMaps
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.GAGA.OpenImmersion

/-!
# Actual canonical source charts on the whole original scheme analytification

The original affine canonical neighbourhood embeds by its ACTUAL algebraic open
inclusion. Analytification of that inclusion is a proved genuine open immersion.
Transporting the PROVED canonical branch isomorphism along its real open image
therefore gives an actual chart of the whole original X^an. No model, GAGA,
algebraic F/H or chart-isomorphism witness is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- Naturality of the actual analytification comparison on genuine scheme points. -/
theorem actual_comparisonBase_map {T X : SchemeLFTℂ.{0}} (f : T ⟶ X)
    (z : analytification.obj T) :
    (analytificationπ X).left.base ((analytification.map f).toLRSHom.base z) =
      f.hom.left ((analytificationπ T).left.base z) :=
  congrArg (fun a : AnalyticSpace.toOverSpec.obj (analytification.obj T) ⟶
    schemeToOverSpec.obj X.obj => a.left.base z) (analytificationπ_naturality f)

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (p : ComplexPoint X)

/-- The SAME original canonical algebraic open inclusion, as a genuine LFT complex scheme morphism. -/
def wholeSchemeChartInclusion : actualEtaleSchemeLFT X d p ⟶ nativeRelativeDimensionLFT X d := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  exact nativeSchemeLFTMap (ComplexPoint.openInclusion X (actualEtaleDatum X d p).neighborhood)

/-- This is the ACTUAL algebraic open immersion, not an assumed analytic chart. -/
instance wholeSchemeChartInclusion_isOpenImmersion :
    IsOpenImmersion (wholeSchemeChartInclusion X d p).hom.left := by
  change IsOpenImmersion (actualEtaleDatum X d p).neighborhood.ι
  infer_instance

/-- The true analytification of the unchanged original algebraic open inclusion. -/
def wholeSchemeAnalyticInclusion : actualChartAnalytification X d p ⟶
    analytification.obj (nativeRelativeDimensionLFT X d) :=
  analytification.map (wholeSchemeChartInclusion X d p)

/-- The actual canonical branch immersion into the whole ORIGINAL X^an. -/
def wholeSchemeBranchImmersion :
    (actualChartAnalytification X d p).restrict (actualChartBranch X d p) ⟶
      analytification.obj (nativeRelativeDimensionLFT X d) :=
  (actualChartAnalytification X d p).ofRestrict (actualChartBranch X d p) ≫
    wholeSchemeAnalyticInclusion X d p

/-- The actual branch immersion is a genuine LRS open immersion. -/
instance wholeSchemeBranchImmersion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (wholeSchemeBranchImmersion X d p).toLRSHom := by
  haveI h₁ : LocallyRingedSpace.IsOpenImmersion
      ((actualChartAnalytification X d p).toLocallyRingedSpace.ofRestrict
        (actualChartBranch X d p).isOpenEmbedding) :=
    LocallyRingedSpace.isOpenImmersion_ofRestrict _ _
  haveI h₂ : LocallyRingedSpace.IsOpenImmersion (wholeSchemeAnalyticInclusion X d p).toLRSHom :=
    isOpenImmersion_analytification_map (wholeSchemeChartInclusion X d p)
  exact LocallyRingedSpace.IsOpenImmersion.comp
    ((actualChartAnalytification X d p).toLocallyRingedSpace.ofRestrict
      (actualChartBranch X d p).isOpenEmbedding)
    (wholeSchemeAnalyticInclusion X d p).toLRSHom

/-- The actual canonical chart branch as an actual open of the whole ORIGINAL analytification. -/
def wholeSchemeChartOpen : Opens (analytification.obj (nativeRelativeDimensionLFT X d)) :=
  analyticOpenImage (wholeSchemeBranchImmersion X d p)

/-- The ACTUAL canonical source-chart isomorphism on the whole original X^an. -/
def wholeSchemeSourceChartIso :
    (analytification.obj (nativeRelativeDimensionLFT X d)).restrict (wholeSchemeChartOpen X d p) ≅
      actualEtaleOkaSource X d p :=
  (analyticOpenImageIso (wholeSchemeBranchImmersion X d p)).symm ≪≫ actualChartIso X d p

/-- The original native affine point transported by the true whole-chart open-image isomorphism. -/
def wholeSchemeChartNativePoint
    (x : (analytification.obj (nativeRelativeDimensionLFT X d)).restrict (wholeSchemeChartOpen X d p)) :
    ComplexPoint X :=
  Point.map (ComplexPoint.openInclusion X (actualEtaleDatum X d p).neighborhood)
    (actualChartNativePoint X d p
      (((analyticOpenImageIso (wholeSchemeBranchImmersion X d p)).inv.toLRSHom.base x).1))

/-- An actual inverse-chart affine point has the SAME original ambient canonical chart inverse. -/
theorem actualEtaleChartPoint_map (w : Fin d → ℂ) :
    Point.map (ComplexPoint.openInclusion X (actualEtaleDatum X d p).neighborhood)
      (actualEtaleChartPoint X d p w) = (ComplexPoint.localChart X d p).symm w :=
  congrArg Subtype.val
    ((ComplexPoint.openHomeomorph X (actualEtaleDatum X d p).neighborhood).apply_symm_apply
      ((ComplexPoint.coordinateNeighborhoodChart X d p).symm w))

/-- The actual whole-chart coordinates realize precisely the original native canonical point. -/
theorem wholeSchemeSourceChartIso_native
    (x : (analytification.obj (nativeRelativeDimensionLFT X d)).restrict (wholeSchemeChartOpen X d p)) :
    (ComplexPoint.localChart X d p).symm
      ((affineCoordinateULift d).symm (((wholeSchemeSourceChartIso X d p).hom.toLRSHom.base x).1)) =
        wholeSchemeChartNativePoint X d p x := by
  let v := (analyticOpenImageIso (wholeSchemeBranchImmersion X d p)).inv.toLRSHom.base x
  have hv : actualEtaleChartPoint X d p
      ((affineCoordinateULift d).symm (((actualChartReverse X d p).toLRSHom.base v).1)) =
      actualChartNativePoint X d p v.1 :=
    (affineChartAnalytic_nativePoint X d p _).symm.trans (actualChartReverse_nativePoint X d p v)
  exact (actualEtaleChartPoint_map X d p _).symm.trans
    (congrArg (Point.map (ComplexPoint.openInclusion X (actualEtaleDatum X d p).neighborhood)) hv)

/-- The true whole-chart original native point lies over the actual global comparison scheme point. -/
theorem wholeSchemeChartNativePoint_underlying
    (x : (analytification.obj (nativeRelativeDimensionLFT X d)).restrict (wholeSchemeChartOpen X d p)) :
    (wholeSchemeChartNativePoint X d p x).underlying =
      (analytificationπ (nativeRelativeDimensionLFT X d)).left.base x.1 := by
  let v := (analyticOpenImageIso (wholeSchemeBranchImmersion X d p)).inv.toLRSHom.base x
  have hi : (wholeSchemeAnalyticInclusion X d p).toLRSHom.base v.1 = x.1 :=
    congrArg (fun f : (analytification.obj (nativeRelativeDimensionLFT X d)).restrict (wholeSchemeChartOpen X d p) ⟶
      analytification.obj (nativeRelativeDimensionLFT X d) => f.toLRSHom.base x)
      (analyticOpenImageIso_inv_fac (wholeSchemeBranchImmersion X d p))
  have hv := affineComparisonPoint_underlying X d p (actualChartAnalytification X d p)
    (actualChartComparison X d p) (actualChartComparison_over X d p) v.1
  exact (congrArg (fun y => (wholeSchemeChartInclusion X d p).hom.left y) hv).trans
    ((actual_comparisonBase_map (wholeSchemeChartInclusion X d p) v.1).symm.trans
      (congrArg (analytificationπ (nativeRelativeDimensionLFT X d)).left.base hi))

end ZInQ.Contrib.CloudB3W17bOkaComparison
