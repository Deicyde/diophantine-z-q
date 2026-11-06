import Mathlib

/-!
# Decimal values of the primorial constants

Blueprint: `syntax/constants/primorial-literal.md`.

The saved specification stores `P_s = 324#` and `W = 4 P_s` as decimal literals. We check
these literals in the kernel: `primorialB` computes `n#` by structural recursion with a
trial-division primality test `isPrimeB`, both proved to agree with Mathlib's `Nat.Prime` and
`primorial`, and the kernel evaluates `primorialB 324` with its GMP-accelerated `Nat`
arithmetic (`decide +kernel`, no `native_decide`).
-/

namespace ZInQ.Syntax

/-- Trial division: `true` iff `n ≥ 2` has no divisor in `[2, n)`. -/
def isPrimeB (n : ℕ) : Bool :=
  2 ≤ n && (List.range' 2 (n - 2)).all fun d => n % d != 0

theorem isPrimeB_iff (n : ℕ) : isPrimeB n = true ↔ n.Prime := by
  rw [Nat.prime_def_lt']
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1,
    bne_iff_ne, ne_eq, Nat.dvd_iff_mod_eq_zero]
  constructor
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m hm hmn => h m ⟨hm, by omega⟩⟩
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m hm => h m hm.1 (by omega)⟩

/-- `n# = ∏_{p ≤ n} p`, computed by structural recursion with the trial-division test. -/
def primorialB : ℕ → ℕ
  | 0 => 1
  | n + 1 => if isPrimeB (n + 1) then (n + 1) * primorialB n else primorialB n

theorem primorialB_eq (n : ℕ) : primorialB n = primorial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold primorial at ih ⊢
    rw [primorialB, ih, Finset.range_add_one (n := n + 1), Finset.filter_insert]
    by_cases h : (n + 1).Prime
    · simp only [(isPrimeB_iff _).2 h, h, ↓reduceIte]
      rw [Finset.prod_insert (by simp)]
    · have hb : isPrimeB (n + 1) = false := by rw [← Bool.not_eq_true, isPrimeB_iff]; exact h
      simp only [hb, h, Bool.false_eq_true, ↓reduceIte]

/-- There are exactly `66` primes `p ≤ 324`. -/
theorem card_primes_le_324 : ((Finset.range 325).filter Nat.Prime).card = 66 := by
  rw [Finset.filter_congr fun n _ => (isPrimeB_iff n).symm]
  decide +kernel

/-- The decimal literal of `P_s = 324#` in the saved specification. -/
theorem primorial_324_eq : primorial 324 =
    19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570 := by
  rw [← primorialB_eq]
  decide +kernel

/-- The decimal literal of `W = 4 P_s` in the saved specification. -/
theorem four_mul_primorial_324_eq : 4 * primorial 324 =
    77445546562803292653885700217249280330651590450286255047627849656860049479426548716387789340974722678430125902516592961137599906280 := by
  rw [primorial_324_eq]

theorem digits_length_eq_of_pow_le_of_lt_pow {n k : ℕ} (h₁ : 2 ^ k ≤ n) (h₂ : n < 2 ^ (k + 1)) :
    (Nat.digits 2 n).length = k + 1 := by
  have hn : n ≠ 0 := (Nat.pos_of_ne_zero (pow_ne_zero k two_ne_zero)).trans_le h₁ |>.ne'
  rw [Nat.length_digits 2 n (by norm_num) hn, Nat.log_eq_of_pow_le_of_lt_pow h₁ h₂]

/-- `P_s` has `433` binary digits. -/
theorem digits_two_primorial_324_length : (Nat.digits 2 (primorial 324)).length = 433 := by
  apply digits_length_eq_of_pow_le_of_lt_pow <;> rw [primorial_324_eq] <;> decide +kernel

/-- `W = 4 P_s` has `435` binary digits. -/
theorem digits_two_four_mul_primorial_324_length :
    (Nat.digits 2 (4 * primorial 324)).length = 435 := by
  apply digits_length_eq_of_pow_le_of_lt_pow <;> rw [four_mul_primorial_324_eq] <;> decide +kernel

end ZInQ.Syntax
