import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Galois.Basic

/-!
# GenusOdd: the discriminant of a quadratic field is a square in it (PROVED)

For a number field `K` of degree two there is `r ∈ K` with `r² = disc K`: with `τ` the nontrivial
automorphism and `b₀, b₁` an integral basis, `disc K = det (Tr(bᵢ bⱼ))` and
`Tr(x y) = x y + τx τy`, so `disc K = (b₀ τb₁ − b₁ τb₀)²`.
-/

noncomputable section

open NumberField

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

theorem sum_aut_eq_of_card_two {K : Type*} [Field K] [Algebra ℚ K] {τ : K ≃ₐ[ℚ] K} (hτ : τ ≠ 1)
    [Fintype (K ≃ₐ[ℚ] K)] (hcard : Fintype.card (K ≃ₐ[ℚ] K) = 2) (x : K) :
    ∑ σ : K ≃ₐ[ℚ] K, σ x = x + τ x := by
  classical
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, τ} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair (Ne.symm hτ), hcard]
  rw [huniv, Finset.sum_pair (Ne.symm hτ)]
  rfl

/-- **`disc K` is a square in a quadratic field `K`** (PROVED). -/
theorem exists_sq_eq_discr {K : Type*} [Field K] [NumberField K] (hK2 : Module.finrank ℚ K = 2) :
    ∃ r : K, r ^ 2 = (discr K : K) := by
  classical
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK2⟩
  have hcardN : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, hK2]
  have hcard : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by rw [← Nat.card_eq_fintype_card, hcardN]
  obtain ⟨τ, hτ⟩ : ∃ τ : K ≃ₐ[ℚ] K, τ ≠ 1 := by
    by_contra h
    push Not at h
    have : Fintype.card (K ≃ₐ[ℚ] K) ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => by
      rw [h a, h b]
    omega
  -- an integral basis indexed by `Fin 2`
  set b0 := integralBasis K
  have hι : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_basis b0, hK2]
  set e := Fintype.equivFinOfCardEq hι
  set b : Fin 2 → K := b0 ∘ e.symm
  have hd : (discr K : ℚ) = Algebra.discr ℚ b := by
    rw [coe_discr]
    exact (Algebra.discr_reindex ℚ b0 e).symm
  have htr : ∀ x : K, algebraMap ℚ K (Algebra.trace ℚ K x) = x + τ x := fun x => by
    rw [trace_eq_sum_automorphisms, sum_aut_eq_of_card_two hτ hcard]
  refine ⟨b 0 * τ (b 1) - b 1 * τ (b 0), ?_⟩
  have : ((discr K : ℚ) : K) = (discr K : K) := by push_cast; rfl
  rw [← this, hd, Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  rw [← eq_ratCast (algebraMap ℚ K)]
  simp only [map_sub, map_mul, htr, map_mul]
  ring

end ZInQ.Contrib.CloudB3RC53.GenusOdd
