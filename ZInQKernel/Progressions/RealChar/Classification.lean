import ZInQKernel.Progressions.RealChar.CRT
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Classification of real Dirichlet characters (plan step 3.1)

Every nontrivial real Dirichlet character `χ` modulo `q` agrees, at the primes `p ∤ 2q`, with the
Legendre symbol `(d / p)` of a squarefree `d ≠ 1` whose absolute value divides `q`; `2 ∣ d` only
if `8 ∣ q`. The proof decomposes `χ` over the prime-power factors of `q`
(`realChar_coprime_mul`), classifies the local characters (`realChar_primePow_odd`,
`realChar_twoPow`), and excludes `d = 1` with Dirichlet's theorem
(`Nat.forall_exists_prime_gt_and_eq_mod`).
-/

namespace ZInQ.Progressions

/-- Every real character (trivial or not) has the data of the classification. -/
theorem realChar_exists_data (q : ℕ) :
    ∀ χ : DirichletCharacter ℂ q, χ ^ 2 = 1 → ∃ d : ℤ, RealCharData q χ d := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rcases eq_or_ne p 2 with rfl | hp2
    · exact realChar_twoPow k
    · exact realChar_primePow_odd hp hp2 hk
  | zero =>
    intro χ _
    exact ⟨1, squarefree_one, by simp, fun _ => dvd_zero 8, fun ℓ _ h => (h (by simp)).elim⟩
  | one => exact realChar_twoPow 0
  | coprime a b _ _ hab ha hb => exact realChar_coprime_mul hab ha hb

/-- **Classification of real characters**, with `|d|` dividing `q`. -/
theorem exists_legendre_of_real_char_dvd {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 = 1) :
    ∃ d : ℤ, Squarefree d ∧ d ≠ 1 ∧ d.natAbs ∣ q ∧ (2 ∣ d → 8 ∣ q) ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * q → χ p = legendreSym p d := by
  obtain ⟨d, hsq, hdvd, h2, hleg⟩ := realChar_exists_data q χ hχ2
  refine ⟨d, hsq, ?_, hdvd, h2, hleg⟩
  rintro rfl
  apply hχ1
  have : NeZero q := ⟨by omega⟩
  refine MulChar.ext fun u => ?_
  obtain ⟨p, hpgt, hp, hpu⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit (2 * q)
  have : Fact p.Prime := ⟨hp⟩
  have hndvd : ¬ p ∣ 2 * q := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  rw [MulChar.one_apply_coe, ← hpu, hleg p hndvd, legendreSym.at_one, Int.cast_one]

/-- **Classification of real characters** (plan step 3.1). For `q ≥ 1` and a Dirichlet character
`χ` modulo `q` with `χ ≠ 1` and `χ ^ 2 = 1`, there is a squarefree `d ≠ 1` with `|d| ≤ q`, every
odd prime factor of `d` dividing `q`, `2 ∣ d` only if `8 ∣ q`, and `χ p = (d / p)` for every prime
`p ∤ 2q`. -/
theorem exists_legendre_of_real_char {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 = 1) :
    ∃ d : ℤ, Squarefree d ∧ d ≠ 1 ∧ d.natAbs ≤ q ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ d → p ∣ q) ∧ (2 ∣ d → 8 ∣ q) ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * q → χ p = legendreSym p d := by
  obtain ⟨d, hsq, hd1, hdvd, h2, hleg⟩ := exists_legendre_of_real_char_dvd hq χ hχ1 hχ2
  exact ⟨d, hsq, hd1, Nat.le_of_dvd hq hdvd,
    fun p _ _ hpd => (Int.natCast_dvd.mp hpd).trans hdvd, h2, hleg⟩

end ZInQ.Progressions
