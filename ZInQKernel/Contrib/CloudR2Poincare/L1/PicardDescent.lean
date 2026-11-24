import ZInQKernel.Contrib.CloudR2Poincare.L1.SheafDescent
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.RationalPoint

/-!
# Genuine normalized line-bundle descent over a quotient

H-72 round 2, L1, Milne AVs §10 (quotient route).

The Picard SHEAF is already available for an arbitrary proper geometrically
integral pointed scheme; its scheme representability is not assumed. A section
compatible with an actual fppf quotient relation descends as a sheaf section.
The proved normalizedPicardIso then supplies an actual normalized invertible
sheaf on the quotient family. This is line-bundle descent, not a desired dual
or representability Fact.

What this does not prove: K(L) is a finite subgroup scheme; the normalized
polarization class is compatible with its relation; the descended bundle has
the general Pic⁰ universal property. Those are distinct remaining geometric
inputs, stated in the lane report.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

open Scheme

/-- A normalized compatible class descends to an actual normalized Picard class.
This theorem assumes only the Picard SHEAF, which is defined for every family. -/
theorem exists_normalizedPicardClass_descent
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    {R T D : Over (Spec (.of k))} (q : T ⟶ D) (t s : R ⟶ T)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (hp : IsPullback t s q q) (M : (pullback f T.hom).Pic)
    (hM : Pic.map (sectionBaseChange f σ hσ T) M = 1)
    (hcompat : (picardFunctor f).obj.map t.op ((toPicardFunctor f).app (.op T) M) =
      (picardFunctor f).obj.map s.op ((toPicardFunctor f).app (.op T) M)) :
    ∃ N : (pullback f D.hom).Pic,
      Pic.map (sectionBaseChange f σ hσ D) N = 1 ∧
      Pic.map (JacobianChallenge.baseChangeMap f q) N = M := by
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  haveI : IsProper (X ↘ Spec (.of k)) := by change IsProper f; infer_instance
  haveI : GeometricallyIntegral (X ↘ Spec (.of k)) := by
    change GeometricallyIntegral f
    infer_instance
  let e : (picardFunctorNormalized f σ hσ).toFunctor ≅ (picardFunctor f).obj :=
    normalizedPicardIso (source := X) σ hσ
  let M' : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T) := ⟨M, hM⟩
  have heM : e.hom.app (.op T) M' = (toPicardFunctor f).app (.op T) M := by
    rw [show e.hom = (picardFunctorNormalized f σ hσ).ι ≫ toPicardFunctor f from
      normalizedPicardIso_hom σ hσ]
    rfl
  obtain ⟨x, hx, _⟩ := fppf_section_descent_of_kernelPair (picardFunctor f)
    q t s hp ((toPicardFunctor f).app (.op T) M) hcompat
  let N' := e.inv.app (.op D) x
  have hN : (picardFunctorNormalized f σ hσ).toFunctor.map q.op N' = M' := by
    rw [show N' = e.inv.app (.op D) x from rfl, ← e.inv.naturality_apply, hx, ← heM]
    exact ConcreteCategory.congr_hom (e.hom_inv_id_app (.op T)) M'
  exact ⟨N'.val, N'.property, congrArg Subtype.val hN⟩

/-- The descended class supplies an actual invertible module sheaf and an actual
pullback isomorphism. No representing Picard scheme is an input. -/
theorem exists_invertibleSheaf_descent
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    {R T D : Over (Spec (.of k))} (q : T ⟶ D) (t s : R ⟶ T)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (hp : IsPullback t s q q) (M : (pullback f T.hom).Modules) [M.IsInvertible]
    (hM : Pic.map (sectionBaseChange f σ hσ T) (Pic.mk M) = 1)
    (hcompat : (picardFunctor f).obj.map t.op ((toPicardFunctor f).app (.op T) (Pic.mk M)) =
      (picardFunctor f).obj.map s.op ((toPicardFunctor f).app (.op T) (Pic.mk M))) :
    ∃ (N : (pullback f D.hom).Modules) (hN : N.IsInvertible),
      Nonempty ((Modules.pullback (JacobianChallenge.baseChangeMap f q)).obj N ≅ M) ∧
      @Pic.map _ _ (sectionBaseChange f σ hσ D) (@Pic.mk _ N hN) = 1 := by
  obtain ⟨Nclass, hnormalized, hpullback⟩ := exists_normalizedPicardClass_descent f σ hσ
    q t s hp (Pic.mk M) hM hcompat
  let N := (fromSkeleton (pullback f D.hom).Modules).obj Nclass.val
  haveI : N.IsInvertible := Pic.isInvertible Nclass
  refine ⟨N, inferInstance, ?_, ?_⟩
  · apply (Pic.mk_eq_mk_iff _ _).mp
    rw [← Pic.map_mk, Pic.mk_fromSkeleton]
    exact hpullback
  · rw [Pic.mk_fromSkeleton]
    exact hnormalized

end ZInQ.Contrib.CloudR2Poincare.L1
