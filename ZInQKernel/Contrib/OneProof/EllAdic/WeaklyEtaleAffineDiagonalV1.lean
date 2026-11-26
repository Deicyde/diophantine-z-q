import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RC53.EllAdic

universe u

/-- The affine weakly étale condition is flatness of the given map and of
its actual diagonal multiplication, with the algebra structure of that map. -/
theorem weaklyEtale_specMap_iff_flat_lmul
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    WeaklyEtale (Spec.map (CommRingCat.ofHom f)) ↔
      (letI : Algebra A B := f.toAlgebra
       f.Flat ∧
         (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom.Flat) := by
  let : Algebra A B := f.toAlgebra
  let a : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let μ : CommRingCat.of (B ⊗[A] B) ⟶ CommRingCat.of B :=
    CommRingCat.ofHom (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom
  let e := pullbackSpecIso A B B
  let g := Spec.map μ
  have hd : pullback.diagonal (Spec.map a) = g ≫ e.inv := diagonal_SpecMap A B
  have hg : Flat g ↔ μ.hom.Flat := Flat.SpecMap_iff
  have ha : Flat (Spec.map a) ↔ a.hom.Flat := Flat.SpecMap_iff
  let : Flat e.inv := inferInstance
  let : Flat e.hom := inferInstance
  have hcancel : Flat (g ≫ e.inv) ↔ Flat g := by
    constructor
    · intro h
      let : Flat (g ≫ e.inv) := h
      have h' : Flat ((g ≫ e.inv) ≫ e.hom) := Flat.comp _ _
      have heq : (g ≫ e.inv) ≫ e.hom = g := by
        rw [Category.assoc, e.inv_hom_id, Category.comp_id]
      exact heq ▸ h'
    · intro h
      let : Flat g := h
      exact Flat.comp _ _
  change WeaklyEtale (Spec.map a) ↔ a.hom.Flat ∧ μ.hom.Flat
  have hdiag : Flat (pullback.diagonal (Spec.map a)) ↔ μ.hom.Flat := by
    rw [hd]
    exact hcancel.trans hg
  exact ⟨fun h => ⟨ha.mp h.flat, hdiag.mp h.flat_diagonal⟩,
    fun h => ⟨ha.mpr h.1, hdiag.mpr h.2⟩⟩

end RC53.EllAdic
