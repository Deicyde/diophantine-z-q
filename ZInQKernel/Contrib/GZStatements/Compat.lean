import ZInQKernel.Contrib.GZDecomp.Decomp

/-!
# gz-statements: the Heegner hypothesis gives the root-number compatibility of Friedberg–Hoffstein

For a newform `f` of trivial nebentypus and a quadratic character `χ_D` of conductor prime to the
level `N`, `ε(f ⊗ χ_D) = ε(f) χ_D(−N)` (Shimura; Atkin–Li 1978; Iwaniec–Kowalski Prop. 14.20,
UNVERIFIED locator). Friedberg–Hoffstein's nonvanishing theorem needs `ε(f ⊗ χ_D) = +1`. This file
proves the arithmetic half: under the hypotheses of `GZDecomp.FHNonvanishing`
(`D < 0`, `D ≡ 1 mod 4` squarefree, every `p ∣ N` split), `(−N / |D|) = −1` and
`(D, N) = 1`. With `ε(f) = −1` this gives `ε(f ⊗ χ_D) = (−1)(−1) = +1`.

It also checks the two definitions the leaves are stated over: `HeegnerHyp N D` is the classical
splitting condition (`heegnerHyp_iff_split`: `D ≡ 1 mod 8` if `2 ∣ N`, `D` a nonzero square
modulo every odd `p ∣ N`), and `chiD D` is the Kronecker character of `ℚ(√D)` at every prime
(`chiD_prime`, `chiD_two`) and completely multiplicative (`chiD_mul`).
-/

namespace ZInQ.GZStatements

open ZInQ.GZDecomp

theorem natAbs_mod_four_of_isOddImagFundDisc {D : ℤ} (hD : IsOddImagFundDisc D) :
    D.natAbs % 4 = 3 := by
  obtain ⟨h0, h4, -⟩ := hD
  omega

/-- `(m / |D|) = 1` for every `m ≠ 0` whose prime factors split. -/
theorem jacobiSym_eq_one_of_primes {D : ℤ} :
    ∀ m : ℕ, m ≠ 0 → (∀ p : ℕ, p.Prime → p ∣ m → jacobiSym (p : ℤ) D.natAbs = 1) →
      jacobiSym (m : ℤ) D.natAbs = 1 := by
  intro m
  induction m using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; simp
  | prime p hp => intro _ h; exact h p hp dvd_rfl
  | mul a b iha ihb =>
    intro hab h
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    push_cast
    rw [jacobiSym.mul_left, iha ha (fun p hp hpa => h p hp (dvd_mul_of_dvd_left hpa _)),
      ihb hb (fun p hp hpb => h p hp (dvd_mul_of_dvd_right hpb _)), one_mul]

/-- **The Heegner hypothesis gives `χ_D(−N) = −1`.** -/
theorem jacobiSym_neg_level {N : ℕ} (hN : N ≠ 0) {D : ℤ} (hD : IsOddImagFundDisc D)
    (hH : HeegnerHyp N D) : jacobiSym (-(N : ℤ)) D.natAbs = -1 := by
  have h3 := natAbs_mod_four_of_isOddImagFundDisc hD
  have hodd : Odd D.natAbs := Nat.odd_iff.mpr (by omega)
  have hneg : -(N : ℤ) = -1 * N := by ring
  rw [hneg, jacobiSym.mul_left, jacobiSym.at_neg_one hodd,
    jacobiSym_eq_one_of_primes N hN hH, mul_one, ZMod.χ₄_nat_three_mod_four h3]

/-- **The Heegner hypothesis gives `(D, N) = 1`** (for `D ≠ 0`). -/
theorem coprime_of_heegnerHyp {N : ℕ} {D : ℤ} (hD0 : D ≠ 0) (hH : HeegnerHyp N D) :
    Nat.Coprime D.natAbs N := by
  have : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD0⟩
  refine Nat.coprime_of_dvd fun p hp hpD hpN => ?_
  have h := hH p hp hpN
  have h0 : jacobiSym (p : ℤ) D.natAbs = 0 := by
    rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
    intro h1
    have : p ∣ Nat.gcd p D.natAbs := Nat.dvd_gcd dvd_rfl hpD
    rw [h1] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  rw [h0] at h
  exact absurd h (by norm_num)

/-- **The Heegner hypothesis at `2`**: for an odd imaginary fundamental discriminant,
`(2 / |D|) = 1` (that is, `2` splits in `ℚ(√D)`) exactly when `D ≡ 1 (mod 8)`. -/
theorem jacobiSym_two_eq_one_iff {D : ℤ} (hD : IsOddImagFundDisc D) :
    jacobiSym 2 D.natAbs = 1 ↔ D % 8 = 1 := by
  have h3 := natAbs_mod_four_of_isOddImagFundDisc hD
  have hodd : Odd D.natAbs := Nat.odd_iff.mpr (by omega)
  have h0 := hD.1
  rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : D.natAbs % 2 ≠ 0 := by omega
  rw [if_neg h2]
  constructor
  · intro h
    by_cases h7 : D.natAbs % 8 = 1 ∨ D.natAbs % 8 = 7
    · omega
    · rw [if_neg h7] at h; norm_num at h
  · intro h
    rw [if_pos (by omega)]

/-- **`chiD` at an odd prime is the Legendre symbol `(D / p)`** (quadratic reciprocity, using
`|D| ≡ 3 mod 4`). -/
theorem jacobiSym_prime_eq_legendreSym {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {D : ℤ}
    (hD : IsOddImagFundDisc D) : jacobiSym (p : ℤ) D.natAbs = legendreSym p D := by
  have h3 := natAbs_mod_four_of_isOddImagFundDisc hD
  have hoddD : Odd D.natAbs := Nat.odd_iff.mpr (by omega)
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hDeq : D = -((D.natAbs : ℕ) : ℤ) := by have := hD.1; omega
  rw [jacobiSym.legendreSym.to_jacobiSym]
  conv_rhs => rw [hDeq]
  rw [jacobiSym.neg _ hpodd]
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpodd)
  rcases hp4 with h1 | h3p
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 hoddD, ZMod.χ₄_nat_one_mod_four h1,
      one_mul]
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four h3p h3, ZMod.χ₄_nat_three_mod_four h3p,
      neg_one_mul]

/-- **`HeegnerHyp` is the splitting condition.** For an odd imaginary fundamental discriminant
`D`, `HeegnerHyp N D` holds exactly when `D ≡ 1 (mod 8)` if `2 ∣ N`, and `D` is a nonzero square
modulo every odd prime `p ∣ N`: the classical criteria for `p` to split in `ℚ(√D)`. -/
theorem heegnerHyp_iff_split {N : ℕ} {D : ℤ} (hD : IsOddImagFundDisc D) :
    HeegnerHyp N D ↔ (2 ∣ N → D % 8 = 1) ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ N → (D : ZMod p) ≠ 0 ∧ IsSquare (D : ZMod p) := by
  constructor
  · intro h
    refine ⟨fun h2 => (jacobiSym_two_eq_one_iff hD).mp (by exact_mod_cast h 2 Nat.prime_two h2),
      fun p hp hp2 hpN => ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    have hl := h p hp hpN
    rw [jacobiSym_prime_eq_legendreSym hp2 hD] at hl
    have h0 : (D : ZMod p) ≠ 0 := by
      intro h0
      rw [(legendreSym.eq_zero_iff p D).mpr h0] at hl
      exact absurd hl (by norm_num)
    exact ⟨h0, (legendreSym.eq_one_iff p h0).mp hl⟩
  · rintro ⟨h2, hodd⟩ p hp hpN
    by_cases hp2 : p = 2
    · subst hp2
      exact_mod_cast (jacobiSym_two_eq_one_iff hD).mpr (h2 hpN)
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨h0, hsq⟩ := hodd p hp hp2 hpN
      rw [jacobiSym_prime_eq_legendreSym hp2 hD]
      exact (legendreSym.eq_one_iff p h0).mpr hsq

/-! ### `chiD` is the Kronecker character of `ℚ(√D)`

Both `chiD D` and the Kronecker character `n ↦ (D / n)` are completely multiplicative, so they
agree once they agree at the primes: at odd `p` both are the Legendre symbol `(D / p)`
(`jacobiSym_prime_eq_legendreSym`), and at `2` both are `1` for `D ≡ 1 (mod 8)` and `−1` for
`D ≡ 5 (mod 8)` (`chiD_two`). -/

theorem chiD_mul (D : ℤ) (m n : ℕ) : chiD D (m * n) = chiD D m * chiD D n := by
  simp only [chiD]
  push_cast
  rw [jacobiSym.mul_left]
  push_cast
  ring

theorem chiD_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {D : ℤ} (hD : IsOddImagFundDisc D) :
    chiD D p = (legendreSym p D : ℂ) := by
  simp only [chiD]
  rw [jacobiSym_prime_eq_legendreSym hp2 hD]

theorem chiD_two {D : ℤ} (hD : IsOddImagFundDisc D) :
    chiD D 2 = if D % 8 = 1 then 1 else -1 := by
  have h3 := natAbs_mod_four_of_isOddImagFundDisc hD
  have hodd : Odd D.natAbs := Nat.odd_iff.mpr (by omega)
  have h0 := hD.1
  simp only [chiD]
  have e : jacobiSym ((2 : ℕ) : ℤ) D.natAbs = if D % 8 = 1 then 1 else -1 := by
    push_cast
    rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have h2 : D.natAbs % 2 ≠ 0 := by omega
    rw [if_neg h2]
    by_cases h8 : D % 8 = 1
    · rw [if_pos (by omega), if_pos h8]
    · rw [if_neg (by omega), if_neg h8]
  rw [e]
  split_ifs <;> simp

end ZInQ.GZStatements
