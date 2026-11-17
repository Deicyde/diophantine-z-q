import ZInQKernel.Contrib.CloudB3W17bOkaComparison.ActualChartCoordinates
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffinePullbackLaw

/-!
# The actual étale coordinate square of the constructed analytic inverse chart

The actual Γ(V) pullback and genuine coordinate-morphism UP prove ρ∘α = the
actual Euclidean open inclusion. Nothing is inferred merely from a set map.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (p : ComplexPoint X)

/-- The actual Euclidean Oka-open inclusion has the very same restricted sheaf and constants. -/
def actualChartOpenInclusion : actualEtaleOkaSource X d p ⟶ AnalyticSpace.complexAffineSpace d :=
  (AnalyticSpace.complexAffineSpace d).ofRestrict (actualEtaleOkaOpen X d p)

/-- The full Γ pullback law of α against the genuine algebraic comparison. -/
theorem affineChartAnalytic_gamma_pullback :
    (LocallyRingedSpace.Γ.map
      ((affineChartAnalytic X d p).toLRSHom ≫ actualChartComparison X d p).op).hom =
      actualEtaleOkaGlobalPullback X d p := by
  rw [affineChartAnalytic_lrs_fac]
  exact affineChartToNativeLRS_gamma_pullback X d p

/-- The true native affine Γ map sends every actual algebraic coordinate to the
actual Euclidean coordinate section, including the real open-source restriction. -/
theorem actualEtaleOkaGlobalPullback_coordinate (j : ULift.{0} (Fin d)) :
    actualEtaleOkaGlobalPullback X d p
      ((actualEtaleDatum X d p).coordinateRingHomOnOpen (MvPolynomial.X j.down)) =
        AnalyticSpace.coordPullback (actualChartOpenInclusion X d p) j := by
  apply OkaRing.ext
  funext y
  let U := actualEtaleOkaOpen X d p
  have hle : openOkaSectionImage U ⊤ ≤ U :=
    LocallyRingedSpace.imOpen_le (X := _root_.complexAffineSpace.{0} d) U ⊤
  have hyU : y.1 ∈ U := hle y.2
  have hyW : (affineCoordinateULift d).symm y.1 ∈ actualEtaleChartOpen X d p := hyU
  let w : actualEtaleOkaSource X d p := ⟨y.1, hyU⟩
  let r := (actualEtaleDatum X d p).coordinateRingHomOnOpen (MvPolynomial.X j.down)
  have hv := RingHom.congr_fun (affineChartGlobalValue_comp_pullback X d p w) r
  have heval := (actualEtaleDatum X d p).pointAlgHomHomeomorph_apply
    (actualEtaleChartPoint X d p ((affineCoordinateULift d).symm y.1)) r
  have hcoord := actualEtaleGammaPullback_X_eval X d p j.down
    ⟨(affineCoordinateULift d).symm y.1, hyW⟩
  have hl : intrinsicEval (actualEtaleOkaSource X d p) (U := ⊤) w trivial
      (actualEtaleOkaGlobalPullback X d p r) = y.1 j :=
    (intrinsicEval_open d U w ⊤ trivial (actualEtaleOkaGlobalPullback X d p r)).trans
      ((openOkaGermEval_germ U w ⊤ trivial (actualEtaleOkaGlobalPullback X d p r)).symm.trans
        (hv.trans (heval.trans
          ((actualEtaleGammaPullback_eval X d p r ⟨(affineCoordinateULift d).symm y.1, hyW⟩).symm.trans hcoord))))
  have hr : intrinsicEval (actualEtaleOkaSource X d p) (U := ⊤) w trivial
      (AnalyticSpace.coordPullback (actualChartOpenInclusion X d p) j) = y.1 j :=
    (AnalyticSpace.base_eq_eval_coordPullback (actualChartOpenInclusion X d p) w j).symm
  have hs := intrinsicEval_open d U w ⊤ trivial (actualEtaleOkaGlobalPullback X d p r)
  have ht := intrinsicEval_open d U w ⊤ trivial
    (AnalyticSpace.coordPullback (actualChartOpenInclusion X d p) j)
  exact hs.symm.trans (hl.trans (hr.symm.trans ht))

/-- ρ∘α is the genuine open inclusion AS morphism, from the full regular coordinate square. -/
theorem affineChartAnalytic_coordinates :
    affineChartAnalytic X d p ≫ actualChartCoordinates X d p = actualChartOpenInclusion X d p := by
  apply AnalyticSpace.hom_ext_complexAffineSpace
  intro j
  change AnalyticSpace.coordPullback (affineChartAnalytic X d p ≫ actualChartCoordinates X d p) j = _
  rw [AnalyticSpace.coordPullback_comp, actualChartCoordinates_pullback]
  have H := LocallyRingedSpace.Γ_map_comp_apply (affineChartAnalytic X d p).toLRSHom
    (actualChartComparison X d p)
    ((actualEtaleDatum X d p).coordinateRingHomOnOpen (MvPolynomial.X j.down))
  exact H.symm.trans ((RingHom.congr_fun (affineChartAnalytic_gamma_pullback X d p) _).trans
    (actualEtaleOkaGlobalPullback_coordinate X d p j))

end ZInQ.Contrib.CloudB3W17bOkaComparison
