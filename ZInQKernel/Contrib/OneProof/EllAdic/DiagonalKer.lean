import Mathlib.RingTheory.Kaehler.Basic

open scoped TensorProduct

/-- If every element of `B` is in the image of some `ι n`, the extended diagonal
ideals of the stages have supremum equal to the diagonal ideal of `B`. -/
theorem iSup_map_diagonalKer_eq
    (A B : Type*) (Bn : ℕ → Type*)
    [CommRing A] [CommRing B] [Algebra A B]
    [∀ n, CommRing (Bn n)] [∀ n, Algebra A (Bn n)]
    (ι : ∀ n, Bn n →ₐ[A] B)
    (hrepr : ∀ b : B, ∃ (n : ℕ) (x : Bn n), ι n x = b) :
    (⨆ n : ℕ, Ideal.map (Algebra.TensorProduct.map (ι n) (ι n))
      (RingHom.ker (Algebra.TensorProduct.lmul' (S := Bn n) A))) =
      RingHom.ker (Algebra.TensorProduct.lmul' (S := B) A) := by
  have hmap (n : ℕ) (x : Bn n) :
      Algebra.TensorProduct.map (ι n) (ι n)
          ((1 : Bn n) ⊗ₜ[A] x - x ⊗ₜ[A] (1 : Bn n)) =
        (1 : B) ⊗ₜ[A] (ι n x) - (ι n x) ⊗ₜ[A] (1 : B) := by
    simp only [map_sub, Algebra.TensorProduct.map_tmul, map_one]
  change (⨆ n : ℕ, Ideal.map (Algebra.TensorProduct.map (ι n) (ι n))
    (KaehlerDifferential.ideal A (Bn n))) = KaehlerDifferential.ideal A B
  apply le_antisymm
  · refine iSup_le fun n => ?_
    rw [← KaehlerDifferential.span_range_eq_ideal A (Bn n), Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [hmap n x]
    exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal A (ι n x)
  · rw [← KaehlerDifferential.span_range_eq_ideal A B, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    obtain ⟨n, x, rfl⟩ := hrepr b
    change ((1 : B) ⊗ₜ[A] (ι n x) - (ι n x) ⊗ₜ[A] (1 : B)) ∈
      (⨆ m : ℕ, Ideal.map (Algebra.TensorProduct.map (ι m) (ι m))
        (KaehlerDifferential.ideal A (Bn m)))
    rw [← hmap n x]
    refine (le_iSup (fun m : ℕ => Ideal.map (Algebra.TensorProduct.map (ι m) (ι m))
      (KaehlerDifferential.ideal A (Bn m))) n) ?_
    exact Ideal.mem_map_of_mem (Algebra.TensorProduct.map (ι n) (ι n))
      (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal A x)
