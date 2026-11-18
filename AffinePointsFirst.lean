import FinitePointsFirst

/-!
# Finitely many actual rational points on a finite-type affine scheme

The actual Spec morphism determines its algebra homomorphism. For a finite
base field and a finite-type affine algebra, the preceding generator argument
therefore bounds the native rational-point morphism type.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace SemistableGeometry.FinitePoints

variable (k R : Type) [Field k] [CommRing R] [Algebra k R]

abbrev affinePointDomain : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)))

abbrev affineScheme : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))

/-- The genuine algebra map associated to the genuine affine rational point. -/
def pointAlgebraHom (x : affinePointDomain k ⟶ affineScheme k R) : R →ₐ[k] k where
  toRingHom := (Spec.preimage x.left).hom
  commutes' c := by
    have hw : CommRingCat.ofHom (algebraMap k R) ≫ Spec.preimage x.left =
        CommRingCat.ofHom (algebraMap k k) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage]
      exact Over.w x
    exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of k ↦ f.hom c) hw

/-- No surrogate point set is used: actual Spec morphisms give an injective map to actual algebra homomorphisms. -/
theorem pointAlgebraHom_injective : Function.Injective (pointAlgebraHom k R) := by
  intro x y h
  apply Over.OverMorphism.ext
  have he : Spec.preimage x.left = Spec.preimage y.left := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom h
  rw [← Spec.map_preimage x.left, ← Spec.map_preimage y.left, he]

/-- The native rational-point type of the displayed finite-type affine scheme over a finite field is finite. -/
theorem finite_affine_points [Finite k] [Algebra.FiniteType k R] :
    Finite (affinePointDomain k ⟶ affineScheme k R) := by
  let : Finite (R →ₐ[k] k) := finite_algHom_of_finiteType k R k
  exact Finite.of_injective _ (pointAlgebraHom_injective k R)

end SemistableGeometry.FinitePoints
