import ZInQKernel.Contrib.CloudB3W17bOkaComparison.NativeChartNeighborhood
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineAnalytification
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.HolomorphicMapGeneral

/-!
# The genuine canonical étale coordinate morphism on the actual analytification

The actual comparison π pulls back the original canonical Γ(V) coordinate
sections. The genuine Hom(analytic-space, ℂ^d) universal property assembles them
into ρ. Its values are exactly the unchanged native chart coordinates, and the
previously proved original-point continuity constructs the real branch open M.
No compatibility/GAGA or algebraic F/H witness is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- The independently proved intrinsic residue is the canonical actual analytic residue;
only proofs of the same coefficient-field property differ. -/
theorem intrinsicEval_eq_canonical (Z : AnalyticSpace.{0}) {U : Opens Z}
    (x : Z) (hx : x ∈ U) : intrinsicEval Z x hx = Z.eval x hx := rfl

/-- The genuine Euclidean open constructed earlier is the actual canonical analytic restriction. -/
theorem euclideanOpen_eq_restrict (n : ℕ) (U : Opens (_root_.complexAffineSpace.{0} n)) :
    euclideanOpen n U = (AnalyticSpace.complexAffineSpace n).restrict U := rfl

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (p : ComplexPoint X)

abbrev actualChartAnalytification : AnalyticSpace.{0} := analytification.obj (actualEtaleSchemeLFT X d p)

/-- The actual original affine scheme comparison of its true analytification. -/
abbrev actualChartComparison : (actualChartAnalytification X d p).toLocallyRingedSpace ⟶
    (actualEtaleNativeScheme X d p).left.toLocallyRingedSpace :=
  (analytificationπ (actualEtaleSchemeLFT X d p)).left

/-- The genuine comparison square is over the unchanged complex scheme's real lifted base. -/
theorem actualChartComparison_over :
    actualChartComparison X d p ≫ (overULift (actualEtaleNativeScheme X d p)).hom.toLRSHom =
      (actualChartAnalytification X d p).toSpecℂ :=
  Over.w (analytificationπ (actualEtaleSchemeLFT X d p))

/-- EVERY actual canonical étale coordinate section, pulled back by the real comparison Γ map. -/
def actualChartCoordinateSections :
    ULift.{0} (Fin d) → (actualChartAnalytification X d p).presheaf.obj (op ⊤) :=
  fun j => (LocallyRingedSpace.Γ.map (actualChartComparison X d p).op).hom
    ((actualEtaleDatum X d p).coordinateRingHomOnOpen (MvPolynomial.X j.down))

/-- The ACTUAL analytic coordinate morphism ρ furnished by the real coordinate sections. -/
def actualChartCoordinates : actualChartAnalytification X d p ⟶ AnalyticSpace.complexAffineSpace d :=
  (AnalyticSpace.homComplexAffineSpaceEquivGeneral (actualChartAnalytification X d p) d).symm
    (actualChartCoordinateSections X d p)

/-- The genuine coordinate pullbacks are precisely the original canonical regular Γ coordinates. -/
theorem actualChartCoordinates_pullback (j : ULift.{0} (Fin d)) :
    AnalyticSpace.coordPullback (actualChartCoordinates X d p) j = actualChartCoordinateSections X d p j :=
  congrFun ((AnalyticSpace.homComplexAffineSpaceEquivGeneral (actualChartAnalytification X d p) d).apply_symm_apply
    (actualChartCoordinateSections X d p)) j

/-- The ORIGINAL native affine point of the real analytification comparison. -/
abbrev actualChartNativePoint :=
  affineComparisonPoint X d p (actualChartAnalytification X d p)
    (actualChartComparison X d p) (actualChartComparison_over X d p)

/-- The real branch open M uses the SAME original canonical Hodge chart source. -/
abbrev actualChartBranch :=
  comparisonChartNeighborhood X d p (actualChartAnalytification X d p)
    (actualChartComparison X d p) (actualChartComparison_over X d p)

/-- Values of ρ's actual pullbacks are the actual native affine point's defining regular values. -/
theorem actualChartCoordinates_base (x : actualChartAnalytification X d p) (j : ULift.{0} (Fin d)) :
    (actualChartCoordinates X d p).toLRSHom.base x j =
      Point.evaluate ⊤
        ((actualEtaleDatum X d p).coordinateRingHomOnOpen (MvPolynomial.X j.down))
          (actualChartNativePoint X d p x) := by
  have H := AnalyticSpace.base_eq_eval_coordPullback (actualChartCoordinates X d p) x j
  rw [actualChartCoordinates_pullback] at H
  exact H.trans
    (affineComparisonPoint_eval X d p (actualChartAnalytification X d p)
      (actualChartComparison X d p) (actualChartComparison_over X d p) x _).symm

/-- The actual analytic coordinate tuple agrees with the native affine point's algebraic coordinate tuple. -/
theorem actualChartCoordinates_native (x : actualChartAnalytification X d p) :
    (actualChartCoordinates X d p).toLRSHom.base x =
      affineCoordinateULift d ((actualEtaleDatum X d p).analyticCoordinates (actualChartNativePoint X d p x)) := by
  funext j
  exact (actualChartCoordinates_base X d p x j).trans
    ((actualEtaleDatum X d p).analyticCoordinates_apply_eq_evaluate (actualChartNativePoint X d p x) j.down).symm

/-- On the real branch M, the true analytic coordinate morphism is the SAME chosen native chart. -/
theorem actualChartCoordinates_onBranch (x : actualChartBranch X d p) :
    (actualChartCoordinates X d p).toLRSHom.base x.1 =
      affineCoordinateULift d ((ComplexPoint.coordinateNeighborhoodChart X d p)
        (comparisonChartPoint X d p (actualChartAnalytification X d p)
          (actualChartComparison X d p) (actualChartComparison_over X d p) x.1)) := by
  let D := actualEtaleDatum X d p
  let Q := actualChartNativePoint X d p x.1
  let P := comparisonChartPoint X d p (actualChartAnalytification X d p)
    (actualChartComparison X d p) (actualChartComparison_over X d p) x.1
  have hc : (ComplexPoint.coordinateNeighborhoodChart X d p) P = D.ambientAnalyticCoordinates P :=
    D.ambientProjectionChart_apply_of_mem (ComplexPoint.pointInCoordinateNeighborhood X d p) P x.2
  have hq : D.ambientAnalyticCoordinates P = D.analyticCoordinates Q :=
    congrArg D.analyticCoordinates
      ((ComplexPoint.openHomeomorph X D.neighborhood).symm_apply_apply Q)
  exact (actualChartCoordinates_native X d p x.1).trans
    (congrArg (affineCoordinateULift d) (hc.trans hq)).symm

/-- ρ restricted to the ACTUAL branch M lands in the ACTUAL open inverse-chart domain W. -/
theorem actualChartCoordinates_branch_mem (x : actualChartBranch X d p) :
    (actualChartCoordinates X d p).toLRSHom.base x.1 ∈ actualEtaleOkaOpen X d p := by
  rw [actualChartCoordinates_onBranch]
  change (affineCoordinateULift d).symm
      (affineCoordinateULift d ((ComplexPoint.coordinateNeighborhoodChart X d p)
        (comparisonChartPoint X d p (actualChartAnalytification X d p)
          (actualChartComparison X d p) (actualChartComparison_over X d p) x.1))) ∈
    actualEtaleChartOpen X d p
  rw [(affineCoordinateULift d).symm_apply_apply]
  exact comparisonChartNeighborhood_coordinates_mem X d p (actualChartAnalytification X d p)
    (actualChartComparison X d p) (actualChartComparison_over X d p) x

end ZInQ.Contrib.CloudB3W17bOkaComparison
