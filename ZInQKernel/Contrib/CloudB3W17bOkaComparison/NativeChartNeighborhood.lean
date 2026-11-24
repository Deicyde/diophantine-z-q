import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineComparisonTopology

/-!
# The ACTUAL native étale-chart branch as a genuine analytic open neighbourhood

The comparison's original native point map is proved continuous, not granted.
The source is exactly the unchanged canonical Hodge coordinate neighbourhood;
preimages of its real chart source therefore define actual analytic opens.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (p : ComplexPoint X) (Z : AnalyticSpace.{0})
variable (f : Z.toLocallyRingedSpace ⟶ (actualEtaleNativeScheme X d p).left.toLocallyRingedSpace)
variable (hbase : f ≫ (overULift (actualEtaleNativeScheme X d p)).hom.toLRSHom = Z.toSpecℂ)

/-- The true original native comparison point in the SAME canonical ambient coordinate neighbourhood. -/
def comparisonChartPoint : Z → ComplexPoint.coordinateNeighborhood X d p :=
  (ComplexPoint.openHomeomorph X (actualEtaleDatum X d p).neighborhood) ∘
    affineComparisonPoint X d p Z f hbase

/-- This original native coordinate-neighbourhood point map is genuinely continuous. -/
theorem continuous_comparisonChartPoint : Continuous (comparisonChartPoint X d p Z f hbase) :=
  (ComplexPoint.openHomeomorph X (actualEtaleDatum X d p).neighborhood).continuous.comp
    (continuous_affineComparisonPoint X d p Z f hbase)

/-- The real canonical chart's branch, as an ACTUAL analytic source open. -/
def comparisonChartNeighborhood : Opens Z :=
  ⟨(comparisonChartPoint X d p Z f hbase) ⁻¹'
      (ComplexPoint.coordinateNeighborhoodChart X d p).source,
    (ComplexPoint.coordinateNeighborhoodChart X d p).open_source.preimage
      (continuous_comparisonChartPoint X d p Z f hbase)⟩

/-- Membership in this actual analytic open is the original canonical chart-source membership. -/
theorem comparisonChartNeighborhood_mem (x : Z) :
    x ∈ comparisonChartNeighborhood X d p Z f hbase ↔
      comparisonChartPoint X d p Z f hbase x ∈
        (ComplexPoint.coordinateNeighborhoodChart X d p).source := Iff.rfl

/-- The true canonical chart coordinates of a point of this actual open lie in the actual Euclidean chart target. -/
theorem comparisonChartNeighborhood_coordinates_mem
    (x : comparisonChartNeighborhood X d p Z f hbase) :
    (ComplexPoint.coordinateNeighborhoodChart X d p)
      (comparisonChartPoint X d p Z f hbase x.1) ∈ actualEtaleChartOpen X d p :=
  (ComplexPoint.coordinateNeighborhoodChart X d p).map_source x.2

end ZInQ.Contrib.CloudB3W17bOkaComparison
