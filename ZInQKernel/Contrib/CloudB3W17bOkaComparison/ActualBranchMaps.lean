import ZInQKernel.Contrib.CloudB3W17bOkaComparison.ActualCoordinateSquare

/-!
# Actual branch restriction and reverse coordinate morphism of the native chart

Both maps are genuine Oka AnalyticSpace.Hom values obtained from actual open
subspace factorisations. Their original native point realization and the real
coordinate square are proved; no analytic/algebraic compatibility witness.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (p : ComplexPoint X)

/-- The actual native point induced by α is the ORIGINAL inverse-chart point. -/
theorem affineChartAnalytic_nativePoint (w : actualEtaleOkaSource X d p) :
    actualChartNativePoint X d p ((affineChartAnalytic X d p).toLRSHom.base w) =
      actualEtaleChartPoint X d p ((affineCoordinateULift d).symm w.1) := by
  apply (nativePointClosedEquiv (actualEtaleNativeScheme X d p)).injective
  apply Subtype.ext
  exact (affineComparisonPoint_underlying X d p (actualChartAnalytification X d p)
    (actualChartComparison X d p) (actualChartComparison_over X d p)
      ((affineChartAnalytic X d p).toLRSHom.base w)).trans
    ((congrArg (fun f : (actualEtaleOkaSource X d p).toLocallyRingedSpace ⟶
        (actualEtaleNativeScheme X d p).left.toLocallyRingedSpace => f.base w)
      (affineChartAnalytic_lrs_fac X d p)).trans (affineChartToNativeLRS_base X d p w))

/-- α has the SAME original inverse-chart point in the canonical ambient coordinate neighbourhood. -/
theorem affineChartAnalytic_chartPoint (w : actualEtaleOkaSource X d p) :
    comparisonChartPoint X d p (actualChartAnalytification X d p)
      (actualChartComparison X d p) (actualChartComparison_over X d p)
        ((affineChartAnalytic X d p).toLRSHom.base w) =
      (ComplexPoint.coordinateNeighborhoodChart X d p).symm ((affineCoordinateULift d).symm w.1) :=
  (congrArg (ComplexPoint.openHomeomorph X (actualEtaleDatum X d p).neighborhood)
    (affineChartAnalytic_nativePoint X d p w)).trans
      ((ComplexPoint.openHomeomorph X (actualEtaleDatum X d p).neighborhood).apply_symm_apply _)

/-- The ACTUAL analytic α lands in the genuine native-chart branch M. -/
theorem affineChartAnalytic_mem_branch (w : actualEtaleOkaSource X d p) :
    (affineChartAnalytic X d p).toLRSHom.base w ∈ actualChartBranch X d p := by
  change comparisonChartPoint X d p (actualChartAnalytification X d p)
      (actualChartComparison X d p) (actualChartComparison_over X d p)
        ((affineChartAnalytic X d p).toLRSHom.base w) ∈
    (ComplexPoint.coordinateNeighborhoodChart X d p).source
  rw [affineChartAnalytic_chartPoint]
  exact (ComplexPoint.coordinateNeighborhoodChart X d p).map_target w.2

/-- α with its true target restricted to the actual branch M. -/
def actualChartForward : actualEtaleOkaSource X d p ⟶
    (actualChartAnalytification X d p).restrict (actualChartBranch X d p) :=
  AnalyticSpace.liftRestrict (affineChartAnalytic X d p) (actualChartBranch X d p)
    (by rintro _ ⟨w, rfl⟩; exact affineChartAnalytic_mem_branch X d p w)

/-- The actual restricted α has the expected genuine inclusion factorization. -/
theorem actualChartForward_fac :
    actualChartForward X d p ≫ (actualChartAnalytification X d p).ofRestrict (actualChartBranch X d p) =
      affineChartAnalytic X d p :=
  AnalyticSpace.liftRestrict_fac _ _ _

/-- The genuine analytic coordinate morphism restricted to the actual branch M. -/
def actualChartReverse : (actualChartAnalytification X d p).restrict (actualChartBranch X d p) ⟶
    actualEtaleOkaSource X d p :=
  AnalyticSpace.liftRestrict
    ((actualChartAnalytification X d p).ofRestrict (actualChartBranch X d p) ≫ actualChartCoordinates X d p)
    (actualEtaleOkaOpen X d p)
    (by rintro _ ⟨x, rfl⟩; exact actualChartCoordinates_branch_mem X d p x)

/-- The ACTUAL reverse map is over the ACTUAL analytic coordinate morphism. -/
theorem actualChartReverse_fac :
    actualChartReverse X d p ≫ actualChartOpenInclusion X d p =
      (actualChartAnalytification X d p).ofRestrict (actualChartBranch X d p) ≫ actualChartCoordinates X d p :=
  AnalyticSpace.liftRestrict_fac _ _ _

/-- Reverse-chart point coordinates are precisely the original canonical branch coordinates. -/
theorem actualChartReverse_base (x : (actualChartAnalytification X d p).restrict (actualChartBranch X d p)) :
    ((actualChartReverse X d p).toLRSHom.base x).1 =
      (actualChartCoordinates X d p).toLRSHom.base x.1 :=
  congrArg (fun f : (actualChartAnalytification X d p).restrict (actualChartBranch X d p) ⟶
    AnalyticSpace.complexAffineSpace d => f.toLRSHom.base x) (actualChartReverse_fac X d p)

/-- Actual reverse coordinates followed by α give the SAME original native point,
using the true left inverse of the unchanged canonical Hodge chart. -/
theorem actualChartReverse_nativePoint
    (x : (actualChartAnalytification X d p).restrict (actualChartBranch X d p)) :
    actualChartNativePoint X d p
      ((affineChartAnalytic X d p).toLRSHom.base ((actualChartReverse X d p).toLRSHom.base x)) =
        actualChartNativePoint X d p x.1 := by
  let P := comparisonChartPoint X d p (actualChartAnalytification X d p)
    (actualChartComparison X d p) (actualChartComparison_over X d p) x.1
  let C := ComplexPoint.coordinateNeighborhoodChart X d p
  have hcoords : (affineCoordinateULift d).symm ((actualChartReverse X d p).toLRSHom.base x).1 = C P :=
    (congrArg (affineCoordinateULift d).symm (actualChartReverse_base X d p x)).trans
      ((congrArg (affineCoordinateULift d).symm (actualChartCoordinates_onBranch X d p x)).trans
        ((affineCoordinateULift d).symm_apply_apply (C P)))
  exact (affineChartAnalytic_nativePoint X d p _).trans
    ((congrArg (actualEtaleChartPoint X d p) hcoords).trans
      ((congrArg (ComplexPoint.openHomeomorph X (actualEtaleDatum X d p).neighborhood).symm
        (C.left_inv x.2)).trans
          ((ComplexPoint.openHomeomorph X (actualEtaleDatum X d p).neighborhood).symm_apply_apply _)))

end ZInQ.Contrib.CloudB3W17bOkaComparison
