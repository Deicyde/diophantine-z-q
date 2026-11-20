import Mathlib.FieldTheory.Galois.Basic

/-! Algebraic end of the split-prime inclusion argument. On-the-spot calculation (c). -/

namespace ZInQ.Manuscript.RC.CMField2

/-- On the diagonal, the two factors in Kronecker's congruence have the same
zeros. In a residue field either factor forces arithmetic Frobenius to fix the value. -/
theorem pow_eq_of_kronecker_diagonal {k : Type*} [Field k] (p : ℕ) (x : k)
    (h : (x ^ p - x) * (x - x ^ p) = 0) : x ^ p = x := by
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact (sub_eq_zero.mp h).symm

/-- At any prime where reduction separates the chosen value from its conjugate,
fixedness in the residue field implies fixedness upstairs. The hypothesis requiring
a separating prime can be applied separately to each Galois element. -/
theorem mem_of_separating_reductions {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (H : IntermediateField K E) (x : E)
    (h : ∀ σ ∈ H.fixingSubgroup, ∃ (R : Type) (_ : CommRing R)
      (f : R →+* E) (P : Ideal R) (a b : R),
      f a = σ x ∧ f b = x ∧ a - b ∈ P ∧ (f a ≠ f b → a - b ∉ P)) : x ∈ H := by
  rw [← IsGalois.fixedField_fixingSubgroup H, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  obtain ⟨R, _, f, P, a, b, ha, hb, hP, hsep⟩ := h σ hσ
  by_contra! hne
  exact hsep (by simpa [ha, hb] using hne) hP


end ZInQ.Manuscript.RC.CMField2
