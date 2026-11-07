import ZInQKernel.Multiplication.Completeness.Core
import ZInQKernel.Multiplication.Certificate.Guard
import ZInQKernel.Multiplication.Certificate.Multiply

/-!
# Completeness of the multiplication template

Blueprint: `multiplication/completeness/completeness.md`.

For all `a, b ∈ ℤ` the multiplication template accepts `(ι(a), ι(b), ι(ab))`. By the unfolding of
the template it suffices to give the height certificate at `(ι(n₁), ι(n₂), ι(n₃))` with shift
points `ι(c_*), ι(c_* n_i)`, and the guard; the guard passes true triples, and the witnesses of the
height certificate are those of `completeness_core`.

Besides pole completeness and the prime pattern, the statement takes as hypotheses the facts
about the constructors `I` that the specification chapter proves: the fixed-scalar semantics of
`S_{c_*}` (`hS`) and the guard polynomial (`hI`), and `M₀ ≥ 1` (size chapter).
-/

namespace ZInQ.Mult

open Syntax

/-- **Completeness of the multiplication template.** -/
theorem multiply_complete (hPC : PoleCompleteness) (h22 : FixedPrimePattern)
    (hM0 : 1 ≤ Syntax.M0) {E : Type} (I : Constructors E) (T : ℤ)
    (hS : ∀ (m : ℤ) (r : Fin 5 → ℚ),
      (scalarTemplate I Syntax.cstar).Rel (Fin.append (iota m) r) ↔ r = iota (Syntax.cstar * m))
    (hI : I.guard T = guardPoly T) (a b : ℤ) :
    (multiplyTemplate I Syntax.cstar Syntax.ell T).Rel (codes3 (iota a) (iota b) (iota (a * b))) := by
  rw [multiply_rel_iff I _ _ T hS]
  refine ⟨![a, b, a * b], rfl, rfl, rfl, ?_, guard_true_triple I T hI a b⟩
  obtain ⟨B, A, hB, hBA, hA, hBs⟩ := completeness_core hPC h22 hM0 a b
  have hc : (![(Syntax.cstar : ℤ), Syntax.cstar * (![a, b, a * b] : Fin 3 → ℤ) 0,
      Syntax.cstar * (![a, b, a * b] : Fin 3 → ℤ) 1, Syntax.cstar * (![a, b, a * b] : Fin 3 → ℤ) 2]
      : Fin 4 → ℤ) = certShifts ![a, b, a * b] := rfl
  have hℓ : (((Syntax.ell : ℕ) : ℤ) : ℚ) = (Syntax.ell : ℚ) := Int.cast_natCast _
  rw [hc, hℓ]
  have hY : ∀ i : Fin 3, (![iota a, iota b, iota (a * b)] : Fin 3 → Fin 5 → ℚ) i =
      iota ((![a, b, a * b] : Fin 3 → ℤ) i) := by
    intro i; fin_cases i <;> rfl
  refine ⟨fun i k => (A i k : ℚ), fun i => (B i : ℚ), fun i => ⟨?_, ?_, ?_⟩, fun k => ?_⟩
  · show (B i : ℚ) ≠ 0
    exact_mod_cast (hB i).ne'
  · rw [hY]; exact (hBA i).1
  · rw [hY]; exact (hBA i).2
  · have sum3 : ∀ s : Fin 3 → ℚ, ∑ l, s l = s 0 + s 1 + s 2 := fun s => Fin.sum_univ_three s
    fin_cases k <;> simp only [nineQ] <;>
    first
      | (obtain ⟨s, hs, hsl⟩ := hA 0 0; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hA 0 1; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hBs 0; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hA 1 0; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hA 1 1; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hBs 1; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hA 2 0; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hA 2 1; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hBs 2; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)

end ZInQ.Mult
