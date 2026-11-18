import FrobeniusFixedFieldSecond
import AffinePointsFirst

/-!
# Descent of an actual affine geometric point fixed by a field automorphism

A fixed Spec-point gives an actual algebra map whose every coordinate is
fixed by the field automorphism power. Codomain restriction to the genuine
fixed intermediate field constructs the descended Spec-point. No desired
field of definition or fixed-point finiteness is assumed.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace SemistableGeometry.FrobeniusFixed

variable {k L : Type} [Field k] [Field L] [Algebra k L]

abbrev pointDomain : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))

abbrev algebraScheme (R : Type) [CommRing R] [Algebra k R] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))

def algebraPointMap {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f : R →ₐ[k] S) : algebraScheme (k := k) S ⟶ algebraScheme R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (f : R →+* S))) (by
    change Spec.map (CommRingCat.ofHom (f : R →+* S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k S))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, f.comp_algebraMap])

/-- The actual algebra homomorphism represented by the actual affine geometric point. -/
def coordinates (R : Type) [CommRing R] [Algebra k R]
    (x : pointDomain (k := k) (L := L) ⟶ algebraScheme R) : R →ₐ[k] L where
  toRingHom := (Spec.preimage x.left).hom
  commutes' c := by
    have h : CommRingCat.ofHom (algebraMap k R) ≫ Spec.preimage x.left =
        CommRingCat.ofHom (algebraMap k L) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage]
      exact Over.w x
    exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of L ↦ f.hom c) h

/-- Fixedness of the actual point forces every coordinate into the actual fixed intermediate field. -/
theorem coordinates_fixed (σ : L ≃ₐ[k] L) (r : ℕ)
    (R : Type) [CommRing R] [Algebra k R]
    (x : pointDomain (k := k) (L := L) ⟶ algebraScheme R)
    (hx : algebraPointMap (σ ^ r).toAlgHom ≫ x = x) (a : R) :
    (σ ^ r) (coordinates R x a) = coordinates R x a := by
  have h : Spec.preimage x.left ≫ CommRingCat.ofHom ((σ ^ r : L ≃ₐ[k] L) : L →+* L) =
      Spec.preimage x.left := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact congrArg Over.Hom.left hx
  exact congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of L ↦ f.hom a) h

/-- The genuine fixed-field codomain restriction of the point's coordinates. -/
def descendedCoordinates (σ : L ≃ₐ[k] L) (r : ℕ)
    (R : Type) [CommRing R] [Algebra k R]
    (x : pointDomain (k := k) (L := L) ⟶ algebraScheme R)
    (hx : algebraPointMap (σ ^ r).toAlgHom ≫ x = x) : R →ₐ[k] field σ r where
  toFun a := ⟨coordinates R x a, (mem_field_iff σ r _).mpr (coordinates_fixed σ r R x hx a)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  commutes' c := Subtype.ext ((coordinates R x).commutes c)

/-- An actual fixed affine point descends to an actual Spec-point over the genuine fixed intermediate field. -/
theorem affine_point_descends (σ : L ≃ₐ[k] L) (r : ℕ)
    (R : Type) [CommRing R] [Algebra k R]
    (x : pointDomain (k := k) (L := L) ⟶ algebraScheme R)
    (hx : algebraPointMap (σ ^ r).toAlgHom ≫ x = x) :
    ∃ y : algebraScheme (k := k) (field σ r) ⟶ algebraScheme R,
      algebraPointMap (IsScalarTower.toAlgHom k (field σ r) L) ≫ y = x := by
  refine ⟨algebraPointMap (descendedCoordinates σ r R x hx), ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (algebraMap (field σ r) L)) ≫
    Spec.map (CommRingCat.ofHom (descendedCoordinates σ r R x hx : R →+* field σ r)) = x.left
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change Spec.map (Spec.preimage x.left) = x.left
  exact Spec.map_preimage x.left

end SemistableGeometry.FrobeniusFixed
