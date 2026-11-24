import ZInQKernel.Contrib.CloudB3W17bOkaComparison.WholeSchemeCharts

/-!
# Actual native centres of the canonical whole-scheme analytic charts

The centre is constructed by the true canonical Hodge inverse-chart point,
actual α and the actual analytic open inclusion. Its genuine scheme comparison
is the ORIGINAL native complex point. No model or GAGA witness is supplied.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (p : ComplexPoint X)

/-- The SAME original canonical affine chart centre, in the actual Oka coordinate convention. -/
def nativeAffineChartCentre : actualEtaleOkaSource X d p :=
  ⟨affineCoordinateULift d
      ((ComplexPoint.coordinateNeighborhoodChart X d p) (ComplexPoint.pointInCoordinateNeighborhood X d p)),
    by
      change (affineCoordinateULift d).symm
        (affineCoordinateULift d ((ComplexPoint.coordinateNeighborhoodChart X d p)
          (ComplexPoint.pointInCoordinateNeighborhood X d p))) ∈ actualEtaleChartOpen X d p
      rw [(affineCoordinateULift d).symm_apply_apply]
      exact (ComplexPoint.coordinateNeighborhoodChart X d p).map_source
        (ComplexPoint.pointInCoordinateNeighborhood_mem_chart_source X d p)⟩

/-- The actual chart inverse at this centre is exactly the ORIGINAL native point. -/
theorem nativeAffineChartCentre_native :
    Point.map (ComplexPoint.openInclusion X (actualEtaleDatum X d p).neighborhood)
      (actualEtaleChartPoint X d p ((affineCoordinateULift d).symm (nativeAffineChartCentre X d p).1)) = p := by
  let C := ComplexPoint.coordinateNeighborhoodChart X d p
  let P := ComplexPoint.pointInCoordinateNeighborhood X d p
  have hc : (affineCoordinateULift d).symm (nativeAffineChartCentre X d p).1 = C P :=
    (affineCoordinateULift d).symm_apply_apply (C P)
  exact (congrArg (fun w : Fin d → ℂ =>
      Point.map (ComplexPoint.openInclusion X (actualEtaleDatum X d p).neighborhood)
        (actualEtaleChartPoint X d p w)) hc).trans
    ((actualEtaleChartPoint_map X d p (C P)).trans
      (congrArg Subtype.val (C.left_inv (ComplexPoint.pointInCoordinateNeighborhood_mem_chart_source X d p))))

/-- A genuine analytic point in the actual whole-source canonical branch chart. -/
def wholeSchemeChartCentre : analytification.obj (nativeRelativeDimensionLFT X d) :=
  (wholeSchemeBranchImmersion X d p).toLRSHom.base
    ((actualChartForward X d p).toLRSHom.base (nativeAffineChartCentre X d p))

/-- The constructed actual analytic centre lies in the genuine whole-source chart open. -/
theorem wholeSchemeChartCentre_mem :
    wholeSchemeChartCentre X d p ∈ wholeSchemeChartOpen X d p :=
  ⟨(actualChartForward X d p).toLRSHom.base (nativeAffineChartCentre X d p), rfl⟩

/-- The actual comparison of the analytic centre is the ORIGINAL native point's underlying scheme point. -/
theorem wholeSchemeChartCentre_comparison :
    (analytificationπ (nativeRelativeDimensionLFT X d)).left.base (wholeSchemeChartCentre X d p) =
      p.underlying := by
  let w := nativeAffineChartCentre X d p
  let v := (actualChartForward X d p).toLRSHom.base w
  have hf : v.1 = (affineChartAnalytic X d p).toLRSHom.base w :=
    congrArg (fun f : actualEtaleOkaSource X d p ⟶ actualChartAnalytification X d p => f.toLRSHom.base w)
      (actualChartForward_fac X d p)
  have hπ : (actualChartComparison X d p).base ((affineChartAnalytic X d p).toLRSHom.base w) =
      (actualEtaleChartPoint X d p ((affineCoordinateULift d).symm w.1)).underlying :=
    (congrArg (fun f : (actualEtaleOkaSource X d p).toLocallyRingedSpace ⟶
      (actualEtaleNativeScheme X d p).left.toLocallyRingedSpace => f.base w)
      (affineChartAnalytic_lrs_fac X d p)).trans (affineChartToNativeLRS_base X d p w)
  exact (actual_comparisonBase_map (wholeSchemeChartInclusion X d p) v.1).trans
    ((congrArg (fun x => (wholeSchemeChartInclusion X d p).hom.left x)
      ((congrArg (actualChartComparison X d p).base hf).trans hπ)).trans
        (congrArg (fun q : ComplexPoint X => q.underlying) (nativeAffineChartCentre_native X d p)))

end ZInQ.Contrib.CloudB3W17bOkaComparison
