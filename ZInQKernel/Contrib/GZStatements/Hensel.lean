import ZInQKernel.Contrib.GZStatements.Compat

/-!
# gz-statements: `HeegnerHyp` implies Gross–Zagier's Heegner condition `D ≡ β² (mod 4N)`

Gross–Zagier (Invent. Math. 84 (1986), UNVERIFIED locator) state the Heegner hypothesis as
"`D ≡ β² (mod 4N)` for some `β`". The leaves `GZDecomp.FHNonvanishing`,
`GZDecomp.GrossZagierHeegner` (and their restricted forms) use `HeegnerHyp N D` ("every `p ∣ N`
splits in `ℚ(√D)`") with `D` odd. This file proves that the Lean hypothesis implies the
Gross–Zagier one (`exists_sq_mod_four_mul_of_heegnerHyp`): Hensel lifting at odd `p` and at `2`
(where `D ≡ 1 mod 8`), then the Chinese remainder theorem.
-/

namespace ZInQ.GZStatements

open ZInQ.GZDecomp

/-- `D` is a square modulo `m`. -/
def SqMod (D : ℤ) (m : ℕ) : Prop := ∃ β : ℤ, (m : ℤ) ∣ D - β ^ 2

theorem SqMod.of_dvd {D : ℤ} {m m' : ℕ} (h : SqMod D m') (hm : m ∣ m') : SqMod D m := by
  obtain ⟨β, hβ⟩ := h
  exact ⟨β, (Int.natCast_dvd_natCast.mpr hm).trans hβ⟩

/-- **Chinese remainder step.** -/
theorem SqMod.mul {D : ℤ} {a b : ℕ} (hab : Nat.Coprime a b) (ha : SqMod D a) (hb : SqMod D b) :
    SqMod D (a * b) := by
  obtain ⟨βa, hβa⟩ := ha
  obtain ⟨βb, hβb⟩ := hb
  have hco : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
  obtain ⟨u, v, huv⟩ := hco
  set c := βa * (v * b) + βb * (u * a) with hc
  have hca : (a : ℤ) ∣ c - βa := ⟨u * (βb - βa), by rw [hc]; linear_combination βa * huv⟩
  have hcb : (b : ℤ) ∣ c - βb := ⟨v * (βa - βb), by rw [hc]; linear_combination βb * huv⟩
  refine ⟨c, ?_⟩
  push_cast
  refine IsCoprime.mul_dvd ⟨u, v, huv⟩ ?_ ?_
  · have : D - c ^ 2 = (D - βa ^ 2) - (c - βa) * (c + βa) := by ring
    rw [this]
    exact dvd_sub hβa (dvd_mul_of_dvd_left hca _)
  · have : D - c ^ 2 = (D - βb ^ 2) - (c - βb) * (c + βb) := by ring
    rw [this]
    exact dvd_sub hβb (dvd_mul_of_dvd_left hcb _)

/-- **Hensel at an odd prime.** If `D` is a nonzero square mod an odd prime `p`, it is a square
mod every `p^k`. -/
theorem sqMod_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : ℤ} (hD : ¬ (p : ℤ) ∣ D)
    (h1 : SqMod D p) : ∀ k : ℕ, SqMod D (p ^ k) := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  intro k
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    rcases j with _ | j
    · simpa using h1
    obtain ⟨β, m, hm⟩ := ih
    push_cast at hm
    -- `p ∤ 2β`
    have hβ : ¬ (p : ℤ) ∣ 2 * β := by
      intro h
      rcases hpi.dvd_or_dvd h with h2 | hβ
      · have : p ∣ 2 := by exact_mod_cast h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      · apply hD
        have hDβ : D = β ^ 2 + (p : ℤ) ^ (j + 1) * m := by linear_combination hm
        rw [hDβ]
        exact dvd_add (dvd_pow hβ two_ne_zero) (dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _)
    obtain ⟨u, v, huv⟩ := (hpi.coprime_iff_not_dvd.mpr hβ).symm
    refine ⟨β + m * u * (p : ℤ) ^ (j + 1), m * v - m ^ 2 * u ^ 2 * (p : ℤ) ^ j, ?_⟩
    push_cast
    linear_combination hm - ((p : ℤ) ^ (j + 1) * m) * huv

/-- **Hensel at `2`.** If `D ≡ 1 (mod 8)`, `D` is a square mod every `2^k`. -/
theorem sqMod_two_pow {D : ℤ} (hD : D % 8 = 1) : ∀ k : ℕ, SqMod D (2 ^ k) := by
  have h3 : ∀ j : ℕ, SqMod D (2 ^ (j + 3)) := by
    intro j
    induction j with
    | zero => exact ⟨1, by norm_num; omega⟩
    | succ j ih =>
      obtain ⟨β, m, hm⟩ := ih
      push_cast at hm
      have hβodd : Odd β := by
        by_contra h
        rw [Int.not_odd_iff_even] at h
        obtain ⟨t, rfl⟩ := h
        have : D = (t + t) ^ 2 + 2 ^ (j + 3) * m := by linear_combination hm
        have h8 : (8 : ℤ) ∣ 2 ^ (j + 3) * m := by
          rw [pow_add]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
        obtain ⟨q, hq⟩ := h8
        have hD2 : D = 2 * (2 * t ^ 2 + 4 * q) := by linear_combination this + hq
        generalize t ^ 2 = w at hD2
        omega
      rcases Int.even_or_odd m with ⟨e, he⟩ | hmodd
      · exact ⟨β, e, by push_cast; rw [pow_succ]; linear_combination hm + 2 ^ (j + 3) * he⟩
      · obtain ⟨e, he⟩ : Even (m - β) := hmodd.sub_odd hβodd
        refine ⟨β + 2 ^ (j + 2), e - 2 ^ j, ?_⟩
        push_cast
        linear_combination hm + 2 ^ (j + 3) * he
  intro k
  exact (h3 k).of_dvd (pow_dvd_pow 2 (by omega))

/-- **The Heegner hypothesis in Gross–Zagier's form.** If `D` is an odd imaginary fundamental
discriminant and every prime `p ∣ N` splits in `ℚ(√D)` (`HeegnerHyp N D`), then
`D ≡ β² (mod 4N)` for some `β`. -/
theorem exists_sq_mod_four_mul_of_heegnerHyp {N : ℕ} (hN : N ≠ 0) {D : ℤ}
    (hD : IsOddImagFundDisc D) (hH : HeegnerHyp N D) : ∃ β : ℤ, (4 * N : ℤ) ∣ D - β ^ 2 := by
  obtain ⟨h2, hodd⟩ := (heegnerHyp_iff_split hD).mp hH
  have key : ∀ m : ℕ, m ∣ 4 * N → SqMod D m := by
    intro m
    induction m using Nat.recOnPosPrimePosCoprime with
    | prime_pow p k hp hk =>
      intro hpk
      have hp4N : p ∣ 4 * N := (dvd_pow_self p hk.ne').trans hpk
      by_cases hp2 : p = 2
      · subst hp2
        by_cases h2N : 2 ∣ N
        · exact sqMod_two_pow (h2 h2N) k
        · -- `N` odd: `2^k ∣ 4N` forces `2^k ∣ 4`, and `D ≡ 1 (mod 4)`
          have hk4 : 2 ^ k ∣ 4 := by
            have hcop : Nat.Coprime (2 ^ k) N :=
              Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2N)
            exact hcop.dvd_of_dvd_mul_right hpk
          have := hD.2.1
          exact SqMod.of_dvd ⟨1, (D - 1) / 4, by push_cast; omega⟩ hk4
      · have hpN : p ∣ N := by
          rcases (Nat.Prime.dvd_mul hp).mp hp4N with h | h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
              (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h))) hp2
          · exact h
        obtain ⟨h0, r, hr⟩ := hodd p hp hp2 hpN
        have hD' : ¬ (p : ℤ) ∣ D := fun h => h0 ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr h)
        have h1 : SqMod D p := by
          refine ⟨(r.val : ℤ), (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
          have : Fact p.Prime := ⟨hp⟩
          push_cast
          rw [ZMod.natCast_zmod_val, hr]
          ring
        exact sqMod_prime_pow hp hp2 hD' h1 k
    | zero => intro h; exact absurd (Nat.eq_zero_of_zero_dvd h) (by omega)
    | one => intro _; exact ⟨0, by simp⟩
    | coprime a b _ _ hab iha ihb =>
      intro h
      exact SqMod.mul hab (iha ((dvd_mul_right a b).trans h)) (ihb ((dvd_mul_left b a).trans h))
  obtain ⟨β, hβ⟩ := key (4 * N) dvd_rfl
  exact ⟨β, by exact_mod_cast hβ⟩

end ZInQ.GZStatements
