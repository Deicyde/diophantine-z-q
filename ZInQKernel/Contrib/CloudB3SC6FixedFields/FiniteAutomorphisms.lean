import Mathlib.FieldTheory.Galois.Basic

/-! # A fixed-field criterion from a complete finite list of automorphisms

This uses the existing Mathlib automorphism-degree inequality and the converse
of Artin's theorem, at Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. No normality or separability
assumption is smuggled into the hypotheses: enough distinct automorphisms
force the finite extension to be Galois.

For the X6 application the intended index is `Fin 4`. This file does not assert
the existence of the X6 moduli witness, its automorphisms, or its degree bound.
Those concrete inputs must be proved separately.
-/

namespace CloudB3SC6FixedFields

/-- A list of `n` distinct automorphisms exhausts the extension degree if that
finite degree is at most `n`. -/
theorem card_aut_eq_finrank_of_many_automorphisms
    (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {n : ℕ} (σ : Fin n → K ≃ₐ[F] K) (hσ : Function.Injective σ)
    (hdegree : Module.finrank F K ≤ n) :
    Nat.card (K ≃ₐ[F] K) = Module.finrank F K := by
  classical
  rw [Nat.card_eq_fintype_card]
  have hmany : n ≤ Fintype.card (K ≃ₐ[F] K) := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective σ hσ
  exact le_antisymm AlgEquiv.card_le (hdegree.trans hmany)

/-- Enough distinct automorphisms force the finite extension to be Galois. -/
theorem isGalois_of_many_automorphisms
    (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {n : ℕ} (σ : Fin n → K ≃ₐ[F] K) (hσ : Function.Injective σ)
    (hdegree : Module.finrank F K ≤ n) : IsGalois F K :=
  IsGalois.of_card_aut_eq_finrank F K
    (card_aut_eq_finrank_of_many_automorphisms F K σ hσ hdegree)

/-- An element is fixed by a complete list of distinct automorphisms exactly
when it comes from the base field. All extension and degree guards are explicit. -/
theorem fixed_iff_mem_base_of_many_automorphisms
    (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {n : ℕ} (σ : Fin n → K ≃ₐ[F] K) (hσ : Function.Injective σ)
    (hdegree : Module.finrank F K ≤ n) (x : K) :
    (∀ i, σ i x = x) ↔ x ∈ Set.range (algebraMap F K) := by
  classical
  have hmany : n ≤ Fintype.card (K ≃ₐ[F] K) := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective σ hσ
  have hcard : Fintype.card (K ≃ₐ[F] K) = n :=
    le_antisymm (AlgEquiv.card_le.trans hdegree) hmany
  have hsurj : Function.Surjective σ :=
    ((Fintype.bijective_iff_injective_and_card σ).2
      ⟨hσ, by simpa only [Fintype.card_fin] using hcard.symm⟩).surjective
  haveI : IsGalois F K := isGalois_of_many_automorphisms F K σ hσ hdegree
  constructor
  · intro hfixed
    apply (IsGalois.mem_range_algebraMap_iff_fixed (F := F) (E := K) x).2
    intro g
    obtain ⟨i, rfl⟩ := hsurj g
    exact hfixed i
  · rintro ⟨a, rfl⟩ i
    exact (σ i).commutes a

/-- The four-automorphism specialization intended for the X6 sign actions. -/
theorem fixed_iff_mem_base_of_four_automorphisms
    (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (σ : Fin 4 → K ≃ₐ[F] K) (hσ : Function.Injective σ)
    (hdegree : Module.finrank F K ≤ 4) (x : K) :
    (∀ i, σ i x = x) ↔ x ∈ Set.range (algebraMap F K) :=
  fixed_iff_mem_base_of_many_automorphisms F K σ hσ hdegree x

end CloudB3SC6FixedFields
