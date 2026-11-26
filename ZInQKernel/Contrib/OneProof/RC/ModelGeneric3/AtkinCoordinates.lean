import ZInQKernel.Contrib.OneProof.RC.ModelGeneric3.ChartCoordinates
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Model

/-! # The ordered coordinates of the fixed rational involution -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric3

open AlgebraicGeometry CategoryTheory ModularCurve
open ModelGeneric2
open ZInQ.Manuscript.RC
open scoped TauCeti.ExactDivisor

open private chart_mem_finiteChart from
  ZInQKernel.Contrib.OneProof.RC.X0Model3.AffineEval

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

/-- The fixed rational involution takes the full point of the pinned rational
open at τ to the full point at the Atkin–Lehner matrix translate of τ. -/
theorem rationalAtkin_rationalPointAtParameter {Q : ℕ} (hQ : Q ∥ N) (τ : UpperHalfPlane) :
    (Spec.map (CommRingCat.ofHom (rationalPointAtParameter h₂ τ).toRingHom) ≫
      rationalOpenImmersion h₂) ≫ (AtkinRational.rationalAtkin hQ).hom =
    Spec.map (CommRingCat.ofHom
      (rationalPointAtParameter h₂ (AtkinPin.atkinGL hQ • τ)).toRingHom) ≫
        rationalOpenImmersion h₂ := by
  rw [rationalPointAtParameter_openImmersion, rationalPointAtParameter_openImmersion]
  exact congrArg Subtype.val ((AtkinRational.rationalAtkin hQ).chart τ)

/-- On every normalized analytic branch the fixed rational Atkin–Lehner
morphism lands in the finite chart, with source and second coordinates
j(Qτ) and j((N/Q)τ) respectively. -/
theorem rationalAtkin_complexPoint_coordinates {Q : ℕ} [NeZero Q] [NeZero (N / Q)]
    (hQ : Q ∥ N) (τ : UpperHalfPlane) :
    let y := X0Model.complexPoint N τ ≫ (AtkinRational.rationalAtkin hQ).hom
    ∃ hy : y (default : Spec (.of ℂ)) ∈ X0Model3.finiteChart N,
      y ≫ X0Model2.jProjection N = X0Model2.jLinePoint (Rat.castHom ℂ)
        (X0Model.analyticJN Q τ) ∧
      X0Model3.affineEval y (X0Model3.finiteChart N) hy (branchQuotientCoordinate h₂) =
        X0Model.analyticJN (N / Q) τ := by
  intro y
  let σ := AtkinPin.atkinGL hQ • τ
  have hy : y = X0Model.complexPoint N σ :=
    congrArg Subtype.val ((AtkinRational.rationalAtkin hQ).chart τ)
  have hmem : y (default : Spec (.of ℂ)) ∈ X0Model3.finiteChart N := by
    rw [hy]
    exact chart_mem_finiteChart N σ
  have hc := AtkinRational.chart_coordinates hQ τ
  refine ⟨hmem, ?_, ?_⟩
  · rw [hy, X0Model2.complexPoint_jProjection]
    exact congrArg (X0Model2.jLinePoint (Rat.castHom ℂ)) hc.1
  · rw [X0Model3.affineEval_congr hmem (chart_mem_finiteChart N σ) hy]
    exact (branchQuotientCoordinate_complexPoint h₂ σ).trans hc.2

#print axioms rationalAtkin_rationalPointAtParameter
#print axioms rationalAtkin_complexPoint_coordinates

end WeierstrassCurve.ModelLevels.ModelGeneric3
