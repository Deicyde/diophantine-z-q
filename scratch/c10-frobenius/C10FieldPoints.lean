import C10FiniteField

set_option autoImplicit false

/-!
# The explicit arithmetic-Frobenius action on field-valued points

Identify q-power Frobenius with the existing q-power automorphism of a perfect
extension of the finite base field. This is not the global Galois/reduction
or Tate-module comparison required by C10.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius
open scoped CategoryTheory.MonObj

namespace C10Frobenius.FieldPoints

universe u

variable {k : Type u} [Field k] [Fintype k] (K : Type u) [Field K] [Algebra k K]
  (p f : ℕ) [Fact p.Prime] [CharP k p] [CharP K p] [PerfectRing K p]
  (hcard : Fintype.card k = p ^ f)

omit [CharP k p] in
/-- The spectrum map of arithmetic Frobenius is the f-fold absolute Frobenius. -/
theorem arithmeticFrobenius_specMap :
    Spec.map (CommRingCat.ofHom (arithmeticFrobenius k K p f hcard : K →+* K)) =
      absoluteFrobeniusPow (Spec (.of K)) p
        (Stacks.Frobenius.isInCharacteristic_spec K p) f := by
  apply specMap_eq_absoluteFrobeniusPow
  intro a
  change arithmeticFrobenius k K p f hcard a = a ^ p ^ f
  rw [arithmeticFrobenius_apply, hcard]

/-- On extension-field points, the actual group endomorphism acts by arithmetic Frobenius. -/
theorem endomorphism_onFieldPoints (A : Grp (Over (Spec (.of k))))
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X) :
    (x ≫ (FiniteField.endomorphism p f hcard A).hom.hom).left =
      Spec.map (CommRingCat.ofHom
        (arithmeticFrobenius k K p f hcard : K →+* K)) ≫ x.left := by
  rw [FiniteField.endomorphism_onPoints, arithmeticFrobenius_specMap]
  rfl

omit [CharP k p] [CharP K p] [PerfectRing K p] in
/-- A base-field automorphism acts on the actual extension-field test scheme. -/
def fieldAutomorphismIso (σ : K ≃ₐ[k] K) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  letI : IsIso (Spec.map (CommRingCat.ofHom (σ : K →+* K))) :=
    inferInstanceAs (IsIso (Spec.map σ.toRingEquiv.toCommRingCatIso.hom))
  refine Over.isoMk (asIso (Spec.map (CommRingCat.ofHom (σ : K →+* K)))) ?_
  change Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k K)) = _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact σ.commutes a

omit [CharP k p] in
/-- Arithmetic Frobenius induces an automorphism of the actual group of K-points. -/
def arithmeticPointEquiv (A : Grp (Over (Spec (.of k)))) :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X) ≃*
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X) :=
  ((CategoryTheory.yonedaMonObj A.X).mapIso
    (fieldAutomorphismIso K (arithmeticFrobenius k K p f hcard)).op).monCatIsoToMulEquiv

omit [CharP k p] in
/-- The point automorphism is precomposition by the explicit q-power field automorphism. -/
@[simp] theorem arithmeticPointEquiv_apply (A : Grp (Over (Spec (.of k))))
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X) :
    (arithmeticPointEquiv K p f hcard A x).left =
      Spec.map (CommRingCat.ofHom
        (arithmeticFrobenius k K p f hcard : K →+* K)) ≫ x.left := rfl

/-- The scheme Frobenius action is exactly the induced group automorphism on K-points. -/
theorem endomorphism_eq_arithmeticPointEquiv (A : Grp (Over (Spec (.of k))))
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X) :
    x ≫ (FiniteField.endomorphism p f hcard A).hom.hom =
      arithmeticPointEquiv K p f hcard A x := by
  apply Over.OverMorphism.ext
  rw [endomorphism_onFieldPoints, arithmeticPointEquiv_apply]

/-- Frobenius is bijective on perfect-extension points, not asserted to be a scheme isomorphism. -/
theorem endomorphism_bijective_onFieldPoints (A : Grp (Over (Spec (.of k)))) :
    Function.Bijective (fun x :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X =>
        x ≫ (FiniteField.endomorphism p f hcard A).hom.hom) := by
  simpa only [endomorphism_eq_arithmeticPointEquiv] using
    (arithmeticPointEquiv K p f hcard A).bijective

end C10Frobenius.FieldPoints
