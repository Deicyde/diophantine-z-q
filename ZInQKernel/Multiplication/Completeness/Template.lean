import ZInQKernel.Multiplication.Completeness.Core
import ZInQKernel.Multiplication.Certificate.Spec

/-!
# Completeness of the multiplication template

Blueprint: `multiplication/completeness/completeness.md`.

For all `a, b ∈ ℤ` the multiplication template accepts `(ι(a), ι(b), ι(ab))`. By the unfolding of
the template it suffices to give the height certificate at `(ι(n₁), ι(n₂), ι(n₃))` with shift
points `ι(c_*), ι(c_* n_i)`, and the guard; the guard passes true triples, and the witnesses of the
height certificate are those of `completeness_core`.

The template is `multiplyTemplate specConstructors c_* ℓ₀ T` with the values of the named
constants; they are rewritten to `Syntax.cstar`, `Syntax.ell`, `Syntax.T`
(`FixedConst.value_cstar`, …) and never evaluated.
-/

namespace ZInQ.Mult

open Syntax

/-- **Completeness of the multiplication template.** -/
theorem multiply_complete (hPC : PoleCompleteness) (h22 : SlopeRepresentation) (a b : ℤ) :
    (multiplyTemplate specConstructors FixedConst.cstar.value FixedConst.ell.value
      FixedConst.T.value).Rel (codes3 (iota a) (iota b) (iota (a * b))) := by
  rw [FixedConst.value_cstar, FixedConst.value_ell, FixedConst.value_T]
  rw [multiply_rel_iff specConstructors _ _ _ spec_scalar_cstar_rel_iff]
  refine ⟨![a, b, a * b], rfl, rfl, rfl, ?_, guard_true_triple specConstructors _ rfl a b⟩
  obtain ⟨B, A, hB, hBA, hA, hBs⟩ := completeness_core hPC h22 a b
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
