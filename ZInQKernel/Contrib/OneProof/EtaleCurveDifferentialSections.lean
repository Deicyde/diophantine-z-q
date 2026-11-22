import ZInQKernel.Contrib.OneProof.EtaleCurveDifferentials
import ZInQKernel.Contrib.CloudB3W17Hodge.Port.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.DifferentialsSections

/-! The regular differential section on a chosen étale curve chart is a
unique regular coefficient times the differential of its coordinate. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.LocalEtaleCoordinates

attribute [local instance] overSpecAlgebra

/-- This uses the literal section and coordinate of the complex curve, after
restriction to the chosen étale chart. -/
theorem existsUnique_smul_sectionsD {X : Over (Spec (CommRingCat.of ℂ))}
    [SmoothOfRelativeDimension 1 X.hom] {x : X.left}
    (D : LocalEtaleCoordinates X 1 x)
    (ω : Γ(X.hom.relativeDifferentials, D.neighborhood)) :
    ∃! a : Γ(X.left, D.neighborhood),
      a • X.hom.sectionsD D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0)) = ω := by
  let U := D.neighborhood
  let B := Γ(X.left, U)
  let P := MvPolynomial (Fin 1) ℂ
  let _ : Algebra P B := D.coordinateAlgHom.toRingHom.toAlgebra
  have : IsScalarTower ℂ P B := IsScalarTower.of_algebraMap_eq
    fun z => (D.coordinateAlgHom.commutes z).symm
  have : Algebra.Etale P B := RingHom.etale_algebraMap.mp D.etale
  let e := X.hom.kaehlerSectionsEquiv U (show algebraMap ℂ B = (X.hom.specStructureMap U).hom
    from rfl) D.isAffine
  obtain ⟨a, ha, hUniq⟩ := KaehlerDifferential.existsUnique_smul_D_of_etaleCurve (e.symm ω)
  have hmap (b : B) :
      e (b • KaehlerDifferential.D ℂ B (D.coordinateAlgHom (MvPolynomial.X 0))) =
        b • X.hom.sectionsD U (D.coordinateAlgHom (MvPolynomial.X 0)) := by
    rw [map_smul, X.hom.kaehlerSectionsEquiv_D]
  refine ⟨a, ?_, fun b hb => hUniq b (e.injective ?_)⟩
  · exact (hmap a).symm.trans ((congrArg e ha).trans (e.apply_symm_apply ω))
  · exact (hmap b).trans (hb.trans (e.apply_symm_apply ω).symm)

/-- Restrict an étale curve coordinate to a principal subopen. -/
def restrictBasicOpen {X : Over (Spec (CommRingCat.of ℂ))}
    [SmoothOfRelativeDimension 1 X.hom] {x y : X.left} (D : LocalEtaleCoordinates X 1 x)
    (f : Γ(X.left, D.neighborhood)) (hy : y ∈ X.left.basicOpen f) :
    LocalEtaleCoordinates X 1 y := by
  let W := X.left.basicOpen f
  let h : W ≤ D.neighborhood := X.left.basicOpen_le f
  let ρ := (X.left.presheaf.map (homOfLE h).op).hom
  let _ : Algebra Γ(X.left, D.neighborhood) Γ(X.left, W) := ρ.toAlgebra
  have := D.isAffine.isLocalization_basicOpen f
  have hρ : ρ.Etale := RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway f)
  let j : Γ(X.left, D.neighborhood) →ₐ[ℂ] Γ(X.left, W) :=
    { toRingHom := ρ
      commutes' := fun c => congrArg (fun q => q c) (X.hom.specStructureMap_map h) }
  exact ⟨W, D.isAffine.basicOpen f, hy, j.comp D.coordinateAlgHom, RingHom.Etale.stableUnderComposition _ _ D.etale hρ⟩

end AlgebraicGeometry.LocalEtaleCoordinates

#print axioms AlgebraicGeometry.LocalEtaleCoordinates.existsUnique_smul_sectionsD
