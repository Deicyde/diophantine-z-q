import Mathlib

/-!
# Square denominators

The reduced denominator of a rational number is a perfect square as soon as every negative
`p`-adic valuation is even.
-/

namespace ZInQ.Mult

theorem padicValNat_den_eq {B : ℚ} {p : ℕ} (hp : p.Prime) (h : padicValNat p B.den ≠ 0) :
    padicValRat p B = -(padicValNat p B.den : ℤ) := by
  rcases Rat.num_or_den_zero_padicVal B hp with h0 | h0
  · rw [padicValRat_def, h0]; ring
  · exact absurd h0 h

theorem isSquare_den_of_even {B : ℚ}
    (h : ∀ p : ℕ, p.Prime → padicValRat p B < 0 → Even (padicValRat p B)) : IsSquare B.den := by
  rw [Nat.isSquare_iff_even_factorization]
  intro p hp
  rw [Nat.factorization_def _ hp]
  by_cases h0 : padicValNat p B.den = 0
  · rw [h0]; exact ⟨0, rfl⟩
  · have hv := padicValNat_den_eq hp h0
    have hneg : padicValRat p B < 0 := by rw [hv]; omega
    have he := h p hp hneg
    rw [hv, even_neg] at he
    exact_mod_cast he

end ZInQ.Mult
