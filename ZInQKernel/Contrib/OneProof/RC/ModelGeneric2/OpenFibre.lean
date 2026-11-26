import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.AffineComparison
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.RationalFibre

/-! # The rational open of every admissible pinned model -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ModelGeneric ModelTorsion
open ZInQ.Contrib.CloudW07JacobiansCurves
open ZInQ.Manuscript.RC

open private finiteChart_affine from ZInQKernel.Contrib.OneProof.RC.X0Model3.AffineEval

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

/-- The fixed curve's finite j-chart with its rational structure map. -/
noncomputable def branchFiniteOverQ (N : ℕ) [NeZero N] : Over (Spec (CommRingCat.of ℚ)) :=
  Over.mk ((X0Model3.finiteChart N).ι ≫ X0Model.overQ N)

/-- The isomorphism of the pinned rational scheme with the fixed finite chart. -/
noncomputable def rationalOpenIso :
    (Y0Rational h₂).left ≅ (X0Model3.finiteChart N).toScheme :=
  (Scheme.Spec.mapIso (rationalChartSections h₂).val.toCommRingCatIso.op) ≪≫
    (finiteChart_affine N).isoSpec.symm

/-- On the compact curve this isomorphism gives the pinned open immersion. -/
theorem rationalOpenIso_hom_comp :
    (rationalOpenIso h₂).hom ≫ (X0Model3.finiteChart N).ι = rationalOpenImmersion h₂ := by
  rw [rationalOpenIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rfl

/-- The isomorphism to the fixed finite chart is over the rational numbers. -/
noncomputable def rationalOpenIsoOverQ : Y0Rational h₂ ≅ branchFiniteOverQ N := by
  refine Over.isoMk (rationalOpenIso h₂) ?_
  change (rationalOpenIso h₂).hom ≫ (X0Model3.finiteChart N).ι ≫ X0Model.overQ N =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (Y0RationalAlgebra h₂)))
  obtain ⟨f, hf⟩ := Spec.map_surjective
    ((rationalOpenIso h₂).hom ≫ (X0Model3.finiteChart N).ι ≫ X0Model.overQ N)
  rw [← hf]
  congr 1
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- Every admissible detector has the same open in the fixed rational curve. -/
noncomputable def detectorRationalOpenIso {ell : ℕ} [Fact ell.Prime] (h₅ : 5 ≤ ell)
    (htame : ¬ ell ∣ N * N.totient) :
    Over.mk (pullback.fst (detectorRationalPoint (ell := ell)) (Pinned.Y0Level h₅ htame h₂).hom) ≅
      branchFiniteOverQ N :=
  Y0RationalFibreIso h₅ htame h₂ ≪≫ rationalOpenIsoOverQ h₂

/-- The actual first j-invariant on a complex cyclic pair equals evaluation
of the fixed chart's j-projection on the corresponding complex point. -/
theorem rationalOpen_pairJ (x : Y0RationalAlgebra h₂ →ₐ[ℚ] ℂ) :
    x ((rationalChartSections h₂).val ((X0Model2.jProjection N).app (NormalModel.chart 0)
      (ProjectiveLine.polyEquivChart ℚ 0 Polynomial.X))) = pairJ (rationalPoints h₂ x) := by
  rw [(rationalChartSections h₂).property, rationalPoints_j]
  exact congrArg x (Polynomial.aeval_X (Y0RationalJ h₂))

/-- The pinned level scheme gets its map from the supplied fixed parametrization
of the compact rational curve by restriction along the open immersion. -/
noncomputable def restrictParametrization {T : Scheme} (π : X0Model.curve N ⟶ T) :
    (Y0Rational h₂).left ⟶ T :=
  rationalOpenImmersion h₂ ≫ π

/-- Point evaluation of the transported parametrization agrees with the compact
curve's supplied map after the open immersion. -/
theorem restrictParametrization_point {T : Scheme} (π : X0Model.curve N ⟶ T)
    (x : Spec (CommRingCat.of ℂ) ⟶ (Y0Rational h₂).left) :
    x ≫ restrictParametrization h₂ π = (x ≫ rationalOpenImmersion h₂) ≫ π :=
  (Category.assoc x (rationalOpenImmersion h₂) π).symm

#print axioms branchFiniteOverQ
#print axioms rationalOpenIso
#print axioms rationalOpenIso_hom_comp
#print axioms rationalOpenIsoOverQ
#print axioms detectorRationalOpenIso
#print axioms rationalOpen_pairJ
#print axioms restrictParametrization
#print axioms restrictParametrization_point

end WeierstrassCurve.ModelLevels.ModelGeneric2
