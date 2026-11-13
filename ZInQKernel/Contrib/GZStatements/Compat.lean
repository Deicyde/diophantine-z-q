import ZInQKernel.Contrib.GZDecomp.Decomp

/-!
# gz-statements: the Heegner hypothesis gives the root-number compatibility of Friedberg–Hoffstein

For a newform `f` of trivial nebentypus and a quadratic character `χ_D` of conductor prime to the
level `N`, `ε(f ⊗ χ_D) = ε(f) χ_D(−N)` (Shimura; Atkin–Li 1978; Iwaniec–Kowalski Prop. 14.20,
UNVERIFIED locator). Friedberg–Hoffstein's nonvanishing theorem needs `ε(f ⊗ χ_D) = +1`. This file
proves the arithmetic half: under the hypotheses of `GZDecomp.FHNonvanishing`
(`D < 0`, `D ≡ 1 mod 4` squarefree, every `p ∣ N` split), `(−N / |D|) = −1` and
`(D, N) = 1`. With `ε(f) = −1` this gives `ε(f ⊗ χ_D) = (−1)(−1) = +1`.
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

end ZInQ.GZStatements
