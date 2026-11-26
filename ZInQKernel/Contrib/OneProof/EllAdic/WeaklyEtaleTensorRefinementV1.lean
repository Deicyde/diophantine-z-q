import ZInQKernel.Contrib.OneProof.EllAdic.CountableTensorRefinement
import ZInQKernel.Contrib.OneProof.EllAdic.FaithfullyFlatTensorRefinementV1
import ZInQKernel.Contrib.OneProof.EllAdic.FlatAlgebraDiagonalSequenceV1
import ZInQKernel.Contrib.OneProof.EllAdic.WeaklyEtaleSpecTensorProductV1
import ZInQKernel.Contrib.OneProof.EllAdic.WeaklyEtaleAffineDiagonalV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace RC53.EllAdic

universe u

open CountableTensorRefinement

private theorem weaklyEtale_algebraMap_iff_diagonal (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A B))) ↔
      (algebraMap A B).Flat ∧
        (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom.Flat := by
  let diagonalFlat (algebra : Algebra A B) : Prop :=
    let : Algebra A B := algebra
    (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom.Flat
  have h : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A B))) ↔
      (algebraMap A B).Flat ∧ diagonalFlat (algebraMap A B).toAlgebra :=
    weaklyEtale_specMap_iff_flat_lmul (algebraMap A B)
  have he : (algebraMap A B).toAlgebra = (inferInstance : Algebra A B) := toAlgebra_algebraMap
  have hd : diagonalFlat (algebraMap A B).toAlgebra = diagonalFlat (inferInstance : Algebra A B) :=
    congrArg diagonalFlat he
  exact Iff.trans h (and_congr_right fun _ => Iff.of_eq hd)

variable {A : Type u} [CommRing A] (C : ℕ → CommAlgCat.{u} A)

/-- The finite prefixes of the literal tensor refinement are weakly étale
when the specified affine factors are weakly étale over the same base. -/
theorem weaklyEtale_specTensorPrefix
    (h : ∀ n, WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A (C n))))) :
    ∀ n, WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A (stage C n)))) := by
  intro n
  induction n with
  | zero =>
      change WeaklyEtale (Spec.map (𝟙 (CommRingCat.of A)))
      rw [Spec.map_id]
      let : Etale (𝟙 (Spec (CommRingCat.of A))) := inferInstance
      infer_instance
  | succ n ih =>
      change WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A (stage C n ⊗[A] C n))))
      let : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A (stage C n)))) := ih
      let : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A (C n)))) := h n
      exact weaklyEtale_specTensorProduct A (stage C n) (C n)

/-- The spectrum of the same quotient direct limit is weakly étale over the
original base and retains the actual factor maps of the tensor refinement. -/
theorem weaklyEtale_specTensorRefinement
    (hff : ∀ n, Module.FaithfullyFlat A (C n))
    (hwe : ∀ n, WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A (C n))))) :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A (limit C)))) := by
  let B := limit C
  let ι (n : ℕ) : StageType C n →ₐ[A] B := (toLimit C n).hom
  have hcompat {i j : ℕ} (h : i ≤ j) (x : StageType C i) :
      ι j (transition C i j h x) = ι i x := by
    exact _root_.DirectLimit.Algebra.of_f (R := A) (G := StageType C)
      (T := fun {i j} _ ↦ TransitionHom C i j) (f := transition C) h x
  have hrep (b : B) : ∃ (n : ℕ) (x : StageType C n), ι n x = b := by
    obtain ⟨n, x, hx⟩ := _root_.DirectLimit.exists_eq_mk (transition C) (show LimitType C from b)
    refine ⟨n, x, ?_⟩
    change (⟦(⟨n, x⟩ : Σ i : ℕ, StageType C i)⟧ : LimitType C) = (show LimitType C from b)
    exact hx.symm
  have hdiag (n : ℕ) :
      (Algebra.TensorProduct.lmul' A : StageType C n ⊗[A] StageType C n →ₐ[A] StageType C n).toRingHom.Flat :=
    ((weaklyEtale_algebraMap_iff_diagonal A (StageType C n)).1 (weaklyEtale_specTensorPrefix C hwe n)).2
  apply (weaklyEtale_algebraMap_iff_diagonal A B).2
  refine ⟨(faithfullyFlat_tensorRefinement C hff).flat, ?_⟩
  exact flat_diagonalMultiplication_of_sequence A B (StageType C) ι
    (fun h => transition C _ _ h) hcompat hrep hdiag

end RC53.EllAdic
