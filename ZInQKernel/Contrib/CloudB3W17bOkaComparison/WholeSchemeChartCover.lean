import ZInQKernel.Contrib.CloudB3W17bOkaComparison.WholeNativePoints
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.WholeSchemeChartCentres
import ZInQKernel.Contrib.CloudB3W17bNativeGlue.NativeMapGlue

/-!
# Actual canonical source-chart cover of the original whole analytification

The genuine π closed-point theorem chooses the ORIGINAL native centre at each
actual analytic point. The constructed chart centre has the same real scheme
comparison, so π's proved injectivity puts that point in its actual chart open.
Pointwise reducedness is then a consequence of the ACTUAL chart isomorphisms
and literal holomorphic functions, not an extra hypothesis on the global map.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic
open ZInQ.Contrib.CloudB3W17bNativeGlue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- Every actual analytic point lies in the actual canonical chart at its ORIGINAL native point. -/
theorem wholeSchemeChart_mem_self
    (z : analytification.obj (nativeRelativeDimensionLFT X d)) :
    z ∈ wholeSchemeChartOpen X d (wholeSchemeNativePoint X d z) := by
  let p := wholeSchemeNativePoint X d z
  have hz : wholeSchemeChartCentre X d p = z :=
    analytificationπ_base_injective (nativeRelativeDimensionLFT X d)
      ((wholeSchemeChartCentre_comparison X d p).trans (wholeSchemeNativePoint_underlying X d z))
  exact (congrArg (fun x : analytification.obj (nativeRelativeDimensionLFT X d) =>
    x ∈ wholeSchemeChartOpen X d p) hz).mp (wholeSchemeChartCentre_mem X d p)

/-- The REAL canonical chart opens cover the whole ORIGINAL scheme analytification. -/
theorem wholeSchemeCharts_cover :
    ∀ z : analytification.obj (nativeRelativeDimensionLFT X d), ∃ p : ComplexPoint X,
      z ∈ wholeSchemeChartOpen X d p :=
  fun z => ⟨wholeSchemeNativePoint X d z, wholeSchemeChart_mem_self X d z⟩

/-- Pointwise reducedness is PROVED from the actual canonical source charts and genuine Oka functions. -/
theorem wholeSchemeAnalytification_pointwiseReduced :
    PointwiseReduced (analytification.obj (nativeRelativeDimensionLFT X d)) :=
  pointwiseReduced_of_charts (wholeSchemeChartOpen X d) (wholeSchemeCharts_cover X d)
    (fun p => actualEtaleOkaSource X d p) (wholeSchemeSourceChartIso X d)
    (fun p => euclideanOpen_pointwiseReduced d (actualEtaleOkaOpen X d p))

end ZInQ.Contrib.CloudB3W17bOkaComparison
