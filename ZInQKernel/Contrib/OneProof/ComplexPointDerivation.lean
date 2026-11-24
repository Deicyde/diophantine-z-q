import ZInQKernel.Contrib.CloudB3W17Hodge.Bridge
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.DifferentialsSections
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.RingTheory.Derivation.Basic

/-! Differentiating the evaluation of regular functions at complex points
gives a derivation into the residue field. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Manifold Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Derivation

/-- A differentiable family of complex-valued algebra homomorphisms has a
derivation in each tangent direction at the chosen point. -/
def of_complexManifoldFamily {E H M A : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℂ E H} [IsManifold I 1 M] [CommRing A] [Algebra ℂ A]
    (φ : M → A →ₐ[ℂ] ℂ) (p : M) (v : TangentSpace I p)
    (hf : ∀ a, MDifferentiableAt I 𝓘(ℂ, ℂ) (fun x => φ x a) p) :
    letI : Algebra A ℂ := (φ p).toRingHom.toAlgebra
    Derivation ℂ A ℂ := by
  let _ : Algebra A ℂ := (φ p).toRingHom.toAlgebra
  let D : A → ℂ := fun a => mfderiv I 𝓘(ℂ, ℂ) (fun x => φ x a) p v
  refine {
    toFun := D
    map_add' := ?_
    map_smul' := ?_
    map_one_eq_zero' := ?_
    leibniz' := ?_ }
  · intro a b
    have he : (fun x => φ x (a + b)) = (fun x => φ x a) + (fun x => φ x b) :=
      funext fun x => map_add (φ x) a b
    change mfderiv I 𝓘(ℂ, ℂ) (fun x => φ x (a + b)) p v = D a + D b
    rw [he, mfderiv_add (hf a) (hf b)]
    rfl
  · intro c a
    have he : (fun x => φ x (c • a)) = c • (fun x => φ x a) :=
      funext fun x => (φ x).toLinearMap.map_smul c a
    change mfderiv I 𝓘(ℂ, ℂ) (fun x => φ x (c • a)) p v = c • D a
    rw [he, const_smul_mfderiv (hf a) c]
    rfl
  · have he : (fun x => φ x 1) = fun _ => (1 : ℂ) := funext fun x => map_one (φ x)
    change mfderiv I 𝓘(ℂ, ℂ) (fun x => φ x 1) p v = 0
    rw [he]
    exact congrArg (fun L => L v)
      (hasMFDerivAt_const (I := I) (I' := 𝓘(ℂ, ℂ)) (1 : ℂ) p).mfderiv
  · intro a b
    have he : (fun x => φ x (a * b)) = (fun x => φ x a) * (fun x => φ x b) :=
      funext fun x => map_mul (φ x) a b
    change mfderiv I 𝓘(ℂ, ℂ) (fun x => φ x (a * b)) p v =
      φ p a * D b + φ p b * D a
    rw [he, ((hf a).hasMFDerivAt.mul (hf b).hasMFDerivAt).mfderiv]
    rfl

end Derivation

namespace AlgebraicGeometry.ComplexPoint

attribute [local instance] overSpecAlgebra

variable {X : Over (Spec (CommRingCat.of ℂ))} (U : X.left.Opens)

/-- Evaluation at a complex point on a scheme open is a complex algebra
homomorphism. -/
def sectionEvaluationAlgHom (p : ComplexPoint X) (hp : p.underlying ∈ U) : Γ(X.left, U) →ₐ[ℂ] ℂ where
  toRingHom := (Point.evaluationHom U ⟨p, hp⟩).hom
  commutes' c := by
    change Point.evaluationHom U ⟨p, hp⟩ ((X.hom.specStructureMap U) c) = c
    rw [Point.evaluationHom_apply, CloudB3W17Hodge.evaluate_eq X p U _ hp]
    let h := (Scheme.preimage_eq_top_of_closedPoint_mem p.left hp).ge
    have he : X.hom.specStructureMap U ≫ p.left.appLE U ⊤ h ≫
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = 𝟙 _ := by
      rw [Scheme.Hom.specStructureMap, Category.assoc, ← Category.assoc (X.hom.appLE _ _ _),
        Scheme.Hom.appLE_comp_appLE]
      have hw : p.left ≫ X.hom = 𝟙 _ := p.w
      rw [hw]
      simp [Scheme.Hom.appLE]
    exact congrArg (fun ψ : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ => ψ c) he

theorem sectionEvaluationAlgHom_apply (p : ComplexPoint X) (hp : p.underlying ∈ U) (s) :
    sectionEvaluationAlgHom U p hp s = Point.evaluate U s p :=
  Point.evaluationHom_apply U ⟨p, hp⟩ s

variable {d : ℕ} [SmoothOfRelativeDimension d X.hom]

/-- Regular functions are holomorphic in the actual complex manifold
structure of a smooth scheme. -/
theorem mdifferentiableAt_evaluate (p : ComplexPoint X) (hp : p.underlying ∈ U)
    (s : Γ(X.left, U)) :
    MDifferentiableAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) (Point.evaluate U s) p := by
  let L := localChart X d p
  have hsrc : p ∈ L.source := mem_localChart_source X d p
  have htar : L p ∈ L.target := L.map_source hsrc
  have ha : AnalyticAt ℂ (fun y => Point.evaluate U s (L.symm y)) (L p) := by
    apply analyticAt_localChart_symm_evaluate X d p htar
    rw [L.left_inv hsrc]
    exact hp
  have hmd : MDifferentiableAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) (fun x => L x) p := by
    exact mdifferentiableAt_extChartAt (I := 𝓘(ℂ, Fin d → ℂ)) (x := p) hsrc
  apply (ha.differentiableAt.comp_mdifferentiableAt hmd).congr_of_eventuallyEq
  filter_upwards [L.open_source.mem_nhds hsrc] with q hq
  simp only [Function.comp_apply, L.left_inv hq]

open Classical in
/-- A complex point outside the open is sent to the chosen fallback
evaluation. This does not affect the germ at the point in the open. -/
private def sectionEvaluationFamily (p : ComplexPoint X) (hp : p.underlying ∈ U)
    (q : ComplexPoint X) : Γ(X.left, U) →ₐ[ℂ] ℂ :=
  if hq : q.underlying ∈ U then sectionEvaluationAlgHom U q hq
  else sectionEvaluationAlgHom U p hp

private theorem sectionEvaluationFamily_eventuallyEq (p : ComplexPoint X) (hp : p.underlying ∈ U)
    (s : Γ(X.left, U)) :
    (fun q => sectionEvaluationFamily U p hp q s) =ᶠ[𝓝 p] Point.evaluate U s := by
  filter_upwards [(Point.isOpen_overOpen (X := X) U).mem_nhds hp] with q hq
  change q.underlying ∈ U at hq
  rw [sectionEvaluationFamily, dite_eq_left hq, sectionEvaluationAlgHom_apply]

/-- The derivative of regular functions along a tangent direction on the
actual complex scheme. -/
def sectionDirectionalDerivation (p : ComplexPoint X) (hp : p.underlying ∈ U)
    (v : TangentSpace 𝓘(ℂ, Fin d → ℂ) p) :
    letI : Algebra Γ(X.left, U) ℂ := (sectionEvaluationFamily U p hp p).toRingHom.toAlgebra
    Derivation ℂ Γ(X.left, U) ℂ :=
  Derivation.of_complexManifoldFamily (sectionEvaluationFamily U p hp) p v fun s =>
    (mdifferentiableAt_evaluate U p hp s).congr_of_eventuallyEq
      (sectionEvaluationFamily_eventuallyEq U p hp s)

theorem sectionDirectionalDerivation_apply (p : ComplexPoint X) (hp : p.underlying ∈ U)
    (v : TangentSpace 𝓘(ℂ, Fin d → ℂ) p) (s : Γ(X.left, U)) :
    sectionDirectionalDerivation U p hp v s =
      mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) (Point.evaluate U s) p v := by
  change mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ)
    (fun q => sectionEvaluationFamily U p hp q s) p v = _
  exact congrArg (fun L => L v)
    (((mdifferentiableAt_evaluate U p hp s).hasMFDerivAt).congr_of_eventuallyEq
      (sectionEvaluationFamily_eventuallyEq U p hp s)).mfderiv

/-- Pair a regular differential on an affine open with a tangent direction
at one of its complex points. -/
def differentialSectionPairing (hU : IsAffineOpen U) (p : ComplexPoint X)
    (hp : p.underlying ∈ U) (v : TangentSpace 𝓘(ℂ, Fin d → ℂ) p) :
    letI : Algebra Γ(X.left, U) ℂ := (sectionEvaluationFamily U p hp p).toRingHom.toAlgebra
    Γ(X.hom.relativeDifferentials, U) →ₗ[Γ(X.left, U)] ℂ := by
  let _ : Algebra Γ(X.left, U) ℂ := (sectionEvaluationFamily U p hp p).toRingHom.toAlgebra
  have : IsScalarTower ℂ Γ(X.left, U) ℂ := IsScalarTower.of_algebraMap_eq
    fun c => ((sectionEvaluationFamily U p hp p).commutes c).symm
  let e := X.hom.kaehlerSectionsEquiv U
    (show algebraMap ℂ Γ(X.left, U) = (X.hom.specStructureMap U).hom from rfl) hU
  exact (sectionDirectionalDerivation U p hp v).liftKaehlerDifferential.comp e.symm.toLinearMap

theorem differentialSectionPairing_sectionsD (hU : IsAffineOpen U) (p : ComplexPoint X)
    (hp : p.underlying ∈ U) (v : TangentSpace 𝓘(ℂ, Fin d → ℂ) p) (s : Γ(X.left, U)) :
    differentialSectionPairing U hU p hp v (X.hom.sectionsD U s) =
      mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) (Point.evaluate U s) p v := by
  let _ : Algebra Γ(X.left, U) ℂ := (sectionEvaluationFamily U p hp p).toRingHom.toAlgebra
  have : IsScalarTower ℂ Γ(X.left, U) ℂ := IsScalarTower.of_algebraMap_eq
    fun c => ((sectionEvaluationFamily U p hp p).commutes c).symm
  rw [differentialSectionPairing]
  change (sectionDirectionalDerivation U p hp v).liftKaehlerDifferential
    ((X.hom.kaehlerSectionsEquiv U (show _ = _ from rfl) hU).symm (X.hom.sectionsD U s)) = _
  rw [← X.hom.kaehlerSectionsEquiv_D U rfl hU s, LinearEquiv.symm_apply_apply,
    Derivation.liftKaehlerDifferential_comp_D, sectionDirectionalDerivation_apply]

/-- The pairing of a coefficient times an exact differential is the
evaluated coefficient times the derivative of the function. -/
theorem differentialSectionPairing_smul_sectionsD (hU : IsAffineOpen U) (p : ComplexPoint X)
    (hp : p.underlying ∈ U) (v : TangentSpace 𝓘(ℂ, Fin d → ℂ) p) (a b : Γ(X.left, U)) :
    differentialSectionPairing U hU p hp v (a • X.hom.sectionsD U b) =
      (Point.evaluate U a p •
        mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) (Point.evaluate U b) p) v := by
  let _ : Algebra Γ(X.left, U) ℂ := (sectionEvaluationFamily U p hp p).toRingHom.toAlgebra
  rw [map_smul, differentialSectionPairing_sectionsD, smul_apply]
  change sectionEvaluationFamily U p hp p a * (show ℂ from _) = Point.evaluate U a p * _
  rw [sectionEvaluationFamily, dite_eq_left hp, sectionEvaluationAlgHom_apply]

end AlgebraicGeometry.ComplexPoint

#print axioms AlgebraicGeometry.ComplexPoint.differentialSectionPairing_sectionsD
