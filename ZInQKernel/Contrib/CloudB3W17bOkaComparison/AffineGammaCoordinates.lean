import ZInQKernel.Contrib.CloudB3W17bOkaComparison.NativeAffinePullback

/-!
# Constants and ν-coordinates for the genuine affine chart pullback

These are the algebraic/analytic evaluation squares needed by the affine
analytification universal property.  The map uses the very same algebraic
étale ν as the canonical Hodge chart, not an assumed compatible chart model.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (z : ComplexPoint X)

/-- Constants of the genuine affine coordinate algebra become the same Oka constant sections. -/
theorem actualEtaleGammaPullback_C (c : ℂ) :
    actualEtaleGammaPullback X d z
      ((actualEtaleDatum X d z).coordinateRingHomOnOpen (MvPolynomial.C c)) =
        algebraMap ℂ (OkaRing (actualEtaleChartOpen X d z)) c := by
  let D := actualEtaleDatum X d z
  letI := D.coordinateRingComplexAlgebra
  apply OkaRing.ext
  funext w
  exact (D.pointAlgHomHomeomorph (actualEtaleChartPoint X d z w.1)).commutes c

/-- The actual ν-coordinate pullback evaluates to the Euclidean coordinate on the inverse chart. -/
theorem actualEtaleGammaPullback_X_eval (i : Fin d) (w : actualEtaleChartOpen X d z) :
    OkaRing.evalHom w.2 (actualEtaleGammaPullback X d z
      ((actualEtaleDatum X d z).coordinateRingHomOnOpen (MvPolynomial.X i))) = w.1 i := by
  let D := actualEtaleDatum X d z
  let p := ComplexPoint.pointInCoordinateNeighborhood X d z
  let e := ComplexPoint.coordinateNeighborhoodChart X d z
  have htarget : w.1 ∈ e.target := w.2
  have hsource : e.symm w.1 ∈ e.source := e.map_target htarget
  have he := D.ambientProjectionChart_apply_of_mem p (e.symm w.1) hsource
  have hright := e.right_inv htarget
  calc
    OkaRing.evalHom w.2 (actualEtaleGammaPullback X d z
        (D.coordinateRingHomOnOpen (MvPolynomial.X i))) =
        Point.evaluate ⊤ (D.coordinateRingHomOnOpen (MvPolynomial.X i))
          (actualEtaleChartPoint X d z w.1) := actualEtaleGammaPullback_eval X d z _ w
    _ = D.analyticCoordinates (actualEtaleChartPoint X d z w.1) i :=
      (D.analyticCoordinates_apply_eq_evaluate _ i).symm
    _ = D.ambientAnalyticCoordinates (e.symm w.1) i := rfl
    _ = e (e.symm w.1) i := (congrArg (fun v => v i) he).symm
    _ = w.1 i := congrArg (fun v => v i) hright

end ZInQ.Contrib.CloudB3W17bOkaComparison
