import ZInQKernel.Contrib.CloudB3W17bOkaComparison.WholeSchemeCharts
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.RET.ClosedPoints

/-!
# Original native complex points of the actual whole-scheme analytification

The genuine analytification closed-point theorem and the proved original native
closed-point dictionary construct the point map. Its values and the actual
source-chart coordinates are proved, not supplied as a model-comparison premise.
The canonical RET closed-point source must be source-built before this module.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The genuine comparison sends an actual analytic point to an actual original closed scheme point. -/
def wholeSchemeComparisonClosedPoint
    (z : analytification.obj (nativeRelativeDimensionLFT X d)) : closedPoints X.left :=
  ⟨(analytificationπ (nativeRelativeDimensionLFT X d)).left.base z,
    (range_analytificationπ_base (nativeRelativeDimensionLFT X d)) ▸
      (show (analytificationπ (nativeRelativeDimensionLFT X d)).left.base z ∈
        Set.range (analytificationπ (nativeRelativeDimensionLFT X d)).left.base from ⟨z, rfl⟩)⟩

/-- The ORIGINAL native complex point of the ACTUAL whole-scheme analytification. -/
def wholeSchemeNativePoint
    (z : analytification.obj (nativeRelativeDimensionLFT X d)) : ComplexPoint X := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  exact (nativePointClosedEquiv X).symm (wholeSchemeComparisonClosedPoint X d z)

/-- Its original underlying scheme point is precisely the actual comparison base point. -/
theorem wholeSchemeNativePoint_underlying
    (z : analytification.obj (nativeRelativeDimensionLFT X d)) :
    (wholeSchemeNativePoint X d z).underlying =
      (analytificationπ (nativeRelativeDimensionLFT X d)).left.base z := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  exact congrArg Subtype.val
    ((nativePointClosedEquiv X).apply_symm_apply (wholeSchemeComparisonClosedPoint X d z))

/-- The point map is injective by the genuine analytification closed-point theorem. -/
theorem wholeSchemeNativePoint_injective : Function.Injective (wholeSchemeNativePoint X d) := by
  intro z w h
  apply analytificationπ_base_injective (nativeRelativeDimensionLFT X d)
  exact (wholeSchemeNativePoint_underlying X d z).symm.trans
    ((congrArg Point.underlying h).trans (wholeSchemeNativePoint_underlying X d w))

/-- Every actual whole-source chart has the SAME original native point as the genuine whole comparison. -/
theorem wholeSchemeSourceChartIso_point (p : ComplexPoint X)
    (z : (analytification.obj (nativeRelativeDimensionLFT X d)).restrict (wholeSchemeChartOpen X d p)) :
    wholeSchemeChartNativePoint X d p z = wholeSchemeNativePoint X d z.1 := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  apply (nativePointClosedEquiv X).injective
  exact Subtype.ext ((wholeSchemeChartNativePoint_underlying X d p z).trans
    (wholeSchemeNativePoint_underlying X d z.1).symm)

/-- The actual source chart coordinates realize the ORIGINAL whole native complex point. -/
theorem wholeSchemeSourceChartIso_realization (p : ComplexPoint X)
    (z : (analytification.obj (nativeRelativeDimensionLFT X d)).restrict (wholeSchemeChartOpen X d p)) :
    (ComplexPoint.localChart X d p).symm
      ((affineCoordinateULift d).symm (((wholeSchemeSourceChartIso X d p).hom.toLRSHom.base z).1)) =
        wholeSchemeNativePoint X d z.1 :=
  (wholeSchemeSourceChartIso_native X d p z).trans (wholeSchemeSourceChartIso_point X d p z)

end ZInQ.Contrib.CloudB3W17bOkaComparison
