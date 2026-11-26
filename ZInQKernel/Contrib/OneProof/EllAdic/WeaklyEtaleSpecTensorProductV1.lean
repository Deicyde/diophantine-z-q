import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RC53.EllAdic

universe u

/-- The tensor product of two weakly étale affine maps over the same base is
weakly étale over that base. The map to the base is the actual spectrum of
the structure morphism of the tensor product. -/
theorem weaklyEtale_specTensorProduct (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A C)))] :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] C)))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let e := pullbackSpecIso A B C
  have h₁ : WeaklyEtale (pullback.fst f g) := by
    change WeaklyEtale (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A C))))
    infer_instance
  let : WeaklyEtale (pullback.fst f g) := h₁
  have h₂ : WeaklyEtale f := by
    change WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    infer_instance
  let : WeaklyEtale f := h₂
  have h₃ : WeaklyEtale e.inv := by
    let : Etale e.inv := inferInstance
    infer_instance
  let : WeaklyEtale e.inv := h₃
  have hmap : e.inv ≫ pullback.fst f g ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] C))) := by
    rw [← Category.assoc, show e.inv ≫ pullback.fst f g =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C))
      from pullbackSpecIso_inv_fst A B C]
    change Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B)) = _
    rw [← Spec.map_comp]
    rfl
  rw [← hmap]
  infer_instance

end RC53.EllAdic
