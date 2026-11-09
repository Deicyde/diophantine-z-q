import Mathlib

/-!
# The clearing inequalities

Blueprint: `multiplication/certificate/clearing-arithmetic.md`.

For `B ∈ {1, 4}` and `v ∈ {0, 1, 2}`, with `C = 14B`, `D = 51C`, `E = 52C + v + 4`:
`2E - C - 2D > v` and `2E - C - 2v = 103C + 8 ≥ 4`; moreover `52·56 + 4 = 2916`,
`52·14 + 4 = 732`, `v₂(12) = 2`, `v₃(12) = 1` and `v_p(12) = 0` for primes `p ≥ 5`. The six
cases are checked by `decide`; the identities hold for all `B`, `v` (`clearing_identities`),
and no natural subtraction truncates.
-/

namespace ZInQ.Mult

/-- The two clearing identities for arbitrary `B`, `v`: `2E - C - 2D = C + 2v + 8` and
`2E - C - 2v = 103C + 8`, with no truncation. -/
theorem clearing_identities (B v : ℕ) :
    2 * (52 * (14 * B) + v + 4) - 14 * B - 2 * (51 * (14 * B)) = 14 * B + 2 * v + 8 ∧
      2 * (52 * (14 * B) + v + 4) - 14 * B - 2 * v = 103 * (14 * B) + 8 := by
  omega

theorem padicValNat_two_twelve : padicValNat 2 12 = 2 := by
  rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem padicValNat_three_twelve : padicValNat 3 12 = 1 := by
  rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- `v_p(12) = 0` for every prime `p ≥ 5`. -/
theorem padicValNat_twelve_of_five_le {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    padicValNat p 12 = 0 := by
  refine padicValNat.eq_zero_of_not_dvd fun hd => ?_
  rw [show (12 : ℕ) = 2 * (2 * 3) by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | hd
  · have := Nat.le_of_dvd (by norm_num) h; omega
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · have := Nat.le_of_dvd (by norm_num) h; omega
  · have := Nat.le_of_dvd (by norm_num) h; omega

/-- `v_p(12) ≤ 2` for every prime `p`. -/
theorem padicValNat_twelve_le_two {p : ℕ} (hp : p.Prime) : padicValNat p 12 ≤ 2 := by
  rcases Nat.lt_or_ge p 5 with h | h
  · interval_cases p
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · rw [padicValNat_two_twelve]
    · rw [padicValNat_three_twelve]; norm_num
    · exact absurd hp (by norm_num)
  · rw [padicValNat_twelve_of_five_le hp h]; norm_num

/-- **The clearing inequalities.** -/
theorem clearing_arithmetic :
    (∀ B ∈ ({1, 4} : Finset ℕ), ∀ v ∈ ({0, 1, 2} : Finset ℕ),
      v < 2 * (52 * (14 * B) + v + 4) - 14 * B - 2 * (51 * (14 * B)) ∧
        2 * (52 * (14 * B) + v + 4) - 14 * B - 2 * v = 103 * (14 * B) + 8 ∧
        4 ≤ 103 * (14 * B) + 8) ∧
      52 * 56 + 4 = 2916 ∧ 52 * 14 + 4 = 732 ∧
      padicValNat 2 12 = 2 ∧ padicValNat 3 12 = 1 ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → padicValNat p 12 = 0 :=
  ⟨by decide, rfl, rfl, padicValNat_two_twelve, padicValNat_three_twelve,
    fun _ hp h5 => padicValNat_twelve_of_five_le hp h5⟩

end ZInQ.Mult
