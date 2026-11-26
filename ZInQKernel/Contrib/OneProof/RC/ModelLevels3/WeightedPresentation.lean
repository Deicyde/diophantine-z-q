import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Module.Submodule.Ker

/-! # A grading presented by homogeneous relations -/

namespace WeierstrassCurve.ModelLevels

open MvPolynomial

section Image

variable {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (w : σ → ℤ) (f : MvPolynomial σ R →ₐ[R] S)

/-- The weight spaces of a weighted polynomial presentation are the images
of the homogeneous polynomials. -/
noncomputable def presentationWeight (i : ℤ) : Submodule R S :=
  (weightedHomogeneousSubmodule R w i).map f.toLinearMap

noncomputable instance presentationWeightMonoid : SetLike.GradedMonoid (presentationWeight w f) where
  one_mem := by
    let := weightedGradedAlgebra R w
    exact ⟨1, SetLike.one_mem_graded (weightedHomogeneousSubmodule R w), map_one f⟩
  mul_mem := by
    let := weightedGradedAlgebra R w
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul f a b⟩

private noncomputable def mapPresentationComponent (i : ℤ) :
    weightedHomogeneousSubmodule R w i →ₗ[R] presentationWeight w f i :=
  f.toLinearMap.restrict (fun a ha => ⟨a, ha, rfl⟩)

private noncomputable def presentationComponents :
    MvPolynomial σ R →ₗ[R] DirectSum ℤ (fun i => presentationWeight w f i) :=
  letI := weightedGradedAlgebra R w
  (DirectSum.lmap (mapPresentationComponent w f)).comp
    (DirectSum.decomposeLinearEquiv (weightedHomogeneousSubmodule R w)).toLinearMap

private theorem presentationComponents_apply (p : MvPolynomial σ R) (i : ℤ) :
    ((presentationComponents w f p i : presentationWeight w f i) : S) =
      f (weightedHomogeneousComponent w i p) := by
  let := weightedGradedAlgebra R w
  exact congrArg f (weightedDecomposition.decompose'_apply R w p i)

private theorem coeLinearMap_presentationComponents (p : MvPolynomial σ R) :
    DirectSum.coeLinearMap (presentationWeight w f) (presentationComponents w f p) = f p := by
  let := weightedGradedAlgebra R w
  have he : (DirectSum.coeLinearMap (presentationWeight w f)).comp
      (DirectSum.lmap (mapPresentationComponent w f)) =
      f.toLinearMap.comp (DirectSum.coeLinearMap (weightedHomogeneousSubmodule R w)) := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
    rfl
  change ((DirectSum.coeLinearMap (presentationWeight w f)).comp
    (DirectSum.lmap (mapPresentationComponent w f)))
      (DirectSum.decompose (weightedHomogeneousSubmodule R w) p) = f p
  rw [he, LinearMap.comp_apply]
  exact congrArg f ((DirectSum.decompose (weightedHomogeneousSubmodule R w)).left_inv p)

private theorem presentationComponents_ker
    (hk : ∀ p, f p = 0 → ∀ i, f (weightedHomogeneousComponent w i p) = 0) :
    LinearMap.ker f.toLinearMap ≤ LinearMap.ker (presentationComponents w f) := by
  intro p hp
  apply LinearMap.mem_ker.mpr
  apply DFinsupp.ext
  intro i
  apply Subtype.ext
  exact (presentationComponents_apply w f p i).trans (hk p hp i)

private theorem presentationComponents_surj :
    Function.Surjective (presentationComponents w f) := by
  let := weightedGradedAlgebra R w
  have h : Function.Surjective (DirectSum.lmap (mapPresentationComponent w f)) := by
    rw [DirectSum.lmap_surjective]
    rintro i ⟨x, p, hp, hpx⟩
    exact ⟨⟨p, hp⟩, Subtype.ext hpx⟩
  exact h.comp (DirectSum.decomposeLinearEquiv (weightedHomogeneousSubmodule R w)).surjective

private theorem presentation_isInternal (hf : Function.Surjective f)
    (hk : ∀ p, f p = 0 → ∀ i, f (weightedHomogeneousComponent w i p) = 0) :
    DirectSum.IsInternal (presentationWeight w f) := by
  change Function.Bijective (DirectSum.coeLinearMap (presentationWeight w f))
  constructor
  · let g := DirectSum.coeLinearMap (presentationWeight w f)
    have h0 (s : DirectSum ℤ (fun i => presentationWeight w f i)) (hs : g s = 0) : s = 0 := by
      obtain ⟨p, rfl⟩ := presentationComponents_surj w f s
      have hp : f p = 0 := (coeLinearMap_presentationComponents w f p).symm.trans hs
      exact presentationComponents_ker w f hk hp
    intro s t h
    apply sub_eq_zero.mp
    exact h0 (s - t) (by rw [map_sub, sub_eq_zero.mpr h])
  · intro x
    obtain ⟨p, rfl⟩ := hf x
    exact ⟨presentationComponents w f p, coeLinearMap_presentationComponents w f p⟩

/-- A surjective presentation induces an internal grading if every weighted
component of a relation is again a relation. -/
@[instance_reducible] noncomputable def presentationGradedAlgebra (hf : Function.Surjective f)
    (hk : ∀ p, f p = 0 → ∀ i, f (weightedHomogeneousComponent w i p) = 0) :
    GradedAlgebra (presentationWeight w f) :=
  (presentation_isInternal w f hf hk).gradedAlgebra

end Image

#print axioms presentationWeight
#print axioms presentationWeightMonoid
#print axioms mapPresentationComponent
#print axioms presentationComponents
#print axioms presentationComponents_apply
#print axioms coeLinearMap_presentationComponents
#print axioms presentationComponents_ker
#print axioms presentationComponents_surj
#print axioms presentation_isInternal
#print axioms presentationGradedAlgebra

end WeierstrassCurve.ModelLevels
