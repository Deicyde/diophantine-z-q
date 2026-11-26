import ZInQKernel.Contrib.OneProof.EllAdic.DiagonalKer
import ZInQKernel.Contrib.OneProof.EllAdic.FlatExtendedKernelQuotientV1
import ZInQKernel.Contrib.OneProof.EllAdic.FlatQuotientISupV1

set_option autoImplicit false

open scoped TensorProduct

namespace RC53.EllAdic

private theorem tensorMultiplication_surjective (A B : Type*)
    [CommRing A] [CommRing B] [Algebra A B] :
    Function.Surjective (Algebra.TensorProduct.lmul' (S := B) A).toRingHom := by
  intro x
  refine ⟨(1 : B) ⊗ₜ[A] x, ?_⟩
  change Algebra.TensorProduct.lmul' (S := B) A ((1 : B) ⊗ₜ[A] x) = x
  rw [Algebra.TensorProduct.lmul'_apply_tmul, one_mul]

/-- Flatness of the diagonal multiplication passes from the stated stages to
an algebra represented by those stages. The ring maps in the proof are the
literal multiplications, and the compatibility needed is that of the stage
maps to the target algebra. -/
theorem flat_diagonalMultiplication_of_sequence (A B : Type*) (Bₙ : ℕ → Type*)
    [CommRing A] [CommRing B] [Algebra A B]
    [∀ n, CommRing (Bₙ n)] [∀ n, Algebra A (Bₙ n)]
    (ι : ∀ n, Bₙ n →ₐ[A] B) (step : ∀ {i j}, i ≤ j → Bₙ i →ₐ[A] Bₙ j)
    (hcompat : ∀ {i j} (h : i ≤ j) (x : Bₙ i), ι j (step h x) = ι i x)
    (hrepr : ∀ b : B, ∃ (n : ℕ) (x : Bₙ n), ι n x = b)
    (hflat : ∀ n, (Algebra.TensorProduct.lmul' (S := Bₙ n) A).toRingHom.Flat) :
    (Algebra.TensorProduct.lmul' (S := B) A).toRingHom.Flat := by
  let I (n : ℕ) : Ideal (B ⊗[A] B) := Ideal.map
    (Algebra.TensorProduct.map (ι n) (ι n)) (KaehlerDifferential.ideal A (Bₙ n))
  have hmono : Monotone I := by
    intro i j hij
    change Ideal.map (Algebra.TensorProduct.map (ι i) (ι i))
      (KaehlerDifferential.ideal A (Bₙ i)) ≤ I j
    rw [← KaehlerDifferential.span_range_eq_ideal A (Bₙ i), Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    change Algebra.TensorProduct.map (ι i) (ι i)
        ((1 : Bₙ i) ⊗ₜ[A] x - x ⊗ₜ[A] (1 : Bₙ i)) ∈ I j
    have hmem : Algebra.TensorProduct.map (ι j) (ι j)
        ((1 : Bₙ j) ⊗ₜ[A] step hij x - step hij x ⊗ₜ[A] (1 : Bₙ j)) ∈ I j :=
      Ideal.mem_map_of_mem (Algebra.TensorProduct.map (ι j) (ι j))
        (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal A (step hij x))
    simpa only [map_sub, Algebra.TensorProduct.map_tmul, map_one, hcompat hij x] using hmem
  have hq (n : ℕ) : Module.Flat (B ⊗[A] B) ((B ⊗[A] B) ⧸ I n) :=
    flat_extended_kernelQuotient_of_surjective
      (Algebra.TensorProduct.map (ι n) (ι n)).toRingHom
      (Algebra.TensorProduct.lmul' (S := Bₙ n) A).toRingHom
      (tensorMultiplication_surjective A (Bₙ n)) (hflat n)
  have hsup : (⨆ n, I n) = RingHom.ker (Algebra.TensorProduct.lmul' (S := B) A).toRingHom :=
    iSup_map_diagonalKer_eq A B Bₙ ι hrepr
  apply (flat_surjective_iff_flat_kernelQuotient _ (tensorMultiplication_surjective A B)).2
  rw [← hsup]
  exact flat_quotient_iSup_of_monotone I hmono hq

end RC53.EllAdic
