import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Lifting square roots modulo prime powers

Elementary Hensel lifting over `ℤ`, used to show that a real Dirichlet character is trivial on
squares: a unit which is a square modulo an odd prime `p` is a square modulo every `p ^ k`, and an
integer `≡ 1 (mod 8)` is a square modulo every `2 ^ k`.
-/

namespace ZInQ.Progressions

/-- One Hensel step at an odd prime: a square root of `n` modulo `p ^ (j + 1)` lifts to one
modulo `p ^ (j + 2)`. -/
theorem realChar_sq_lift_step_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n y : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) {j : ℕ} (h : (p : ℤ) ^ (j + 1) ∣ y ^ 2 - n) :
    ∃ y' : ℤ, (p : ℤ) ^ (j + 2) ∣ y' ^ 2 - n := by
  obtain ⟨m, hm⟩ := h
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpy : ¬ (p : ℤ) ∣ y := by
    intro hy
    apply hn
    have h1 : (p : ℤ) ∣ y ^ 2 := dvd_pow hy two_ne_zero
    have h2 : (p : ℤ) ∣ y ^ 2 - n := by
      rw [hm]; exact dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero j)) _
    simpa using dvd_sub h1 h2
  have hp2y : ¬ (p : ℤ) ∣ 2 * y := by
    intro h
    rcases hpr.dvd_or_dvd h with h | h
    · have : p ∣ 2 := by exact_mod_cast h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    · exact hpy h
  obtain ⟨a, b, hab⟩ :=
    ((Irreducible.coprime_iff_not_dvd hpr.irreducible).mpr hp2y).symm
  refine ⟨y - a * m * (p : ℤ) ^ (j + 1), m * b + a ^ 2 * m ^ 2 * (p : ℤ) ^ j, ?_⟩
  linear_combination hm - (m * (p : ℤ) ^ (j + 1)) * hab

/-- Square roots modulo an odd prime lift to every power of that prime. -/
theorem realChar_exists_sq_mod_pow_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n x : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) (hx : (p : ℤ) ∣ x ^ 2 - n) (k : ℕ) :
    ∃ y : ℤ, (p : ℤ) ^ k ∣ y ^ 2 - n := by
  suffices ∀ j : ℕ, ∃ y : ℤ, (p : ℤ) ^ (j + 1) ∣ y ^ 2 - n by
    obtain ⟨y, hy⟩ := this k
    exact ⟨y, (pow_dvd_pow _ (Nat.le_succ k)).trans hy⟩
  intro j
  induction j with
  | zero => exact ⟨x, by simpa using hx⟩
  | succ j ih =>
    obtain ⟨y, hy⟩ := ih
    exact realChar_sq_lift_step_odd hp hp2 hn hy

/-- An integer `≡ 1 (mod 8)` is a square modulo every power of `2`. -/
theorem realChar_exists_sq_mod_two_pow {n : ℤ} (hn : (8 : ℤ) ∣ n - 1) (k : ℕ) :
    ∃ y : ℤ, (2 : ℤ) ^ k ∣ y ^ 2 - n := by
  suffices ∀ j : ℕ, ∃ y : ℤ, (2 : ℤ) ^ (j + 3) ∣ y ^ 2 - n by
    obtain ⟨y, hy⟩ := this k
    exact ⟨y, (pow_dvd_pow _ (Nat.le_add_right k 3)).trans hy⟩
  intro j
  induction j with
  | zero =>
    refine ⟨1, ?_⟩
    obtain ⟨c, hc⟩ := hn
    exact ⟨-c, by linear_combination -hc⟩
  | succ j ih =>
    obtain ⟨y, m, hm⟩ := ih
    obtain ⟨c, hc⟩ := hn
    rcases Int.even_or_odd m with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact ⟨y, s, by rw [hm, hs]; ring⟩
    · have hy2 : Odd (y ^ 2) :=
        ⟨4 * c + 2 ^ (j + 2) * m, by linear_combination hm + hc⟩
      obtain ⟨r, hr⟩ := (Int.odd_pow' two_ne_zero).mp hy2
      refine ⟨y + 2 ^ (j + 2), r + s + 1 + 2 ^ j, ?_⟩
      rw [hr] at hm ⊢
      linear_combination hm + (2 : ℤ) ^ (j + 3) * hs

end ZInQ.Progressions
