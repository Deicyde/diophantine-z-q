import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Defs

/-!
# GenusOdd: integer arithmetic of `d₁ d₂ = D c²` (PROVED)

For `D ≡ 1 (mod 4)` squarefree, `c ≥ 1` prime to `D`, `d₁ ≡ 1 (mod 4)` squarefree with `c ∣ d₁` and
`d₁ d₂ = D c²`:

* `d₂ ≡ 1 (mod 4)` and `d₂` is squarefree;
* a prime `p ∣ c` divides both `d₁` and `d₂`; a prime `p ∤ c` divides at most one of them, and
  divides one of them exactly when `p ∣ D`;
* for `p ∤ c`: `χ_{d₁}(p) χ_{d₂}(p) = χ_D(p)` and, for `p ∤ d`, `χ_d(p²) = 1`, with
  `χ_d(n) = (n / |d|)` (`chiD`).
-/

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

section

variable {D d₁ d₂ : ℤ} {c : ℕ}

theorem odd_of_dvd_one_mod_four {c d : ℤ} (hcd : c ∣ d) (hd : d % 4 = 1) : c % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one c with h | h
  · exfalso
    obtain ⟨m, rfl⟩ := hcd
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
    have h2 : (2 * (k * m)) % 4 = 1 := by rw [← mul_assoc, ← hk]; exact hd
    generalize k * m = t at h2
    omega
  · exact h

/-- `d₂ ≡ 1 (mod 4)` (PROVED). -/
theorem d₂_mod_four (hprod : d₁ * d₂ = D * c ^ 2) (hd₁ : d₁ % 4 = 1) (hD : D % 4 = 1)
    (hcd : (c : ℤ) ∣ d₁) : d₂ % 4 = 1 := by
  have hc := odd_of_dvd_one_mod_four hcd hd₁
  have h : (d₁ * d₂) % 4 = (D * (c : ℤ) ^ 2) % 4 := by rw [hprod]
  rw [Int.mul_emod, hd₁, Int.mul_emod D, hD, pow_two, Int.mul_emod (c : ℤ)] at h
  have hc4 : (c : ℤ) % 4 = 1 ∨ (c : ℤ) % 4 = 3 := by omega
  have h4 : d₂ % 4 = 0 ∨ d₂ % 4 = 1 ∨ d₂ % 4 = 2 ∨ d₂ % 4 = 3 := by omega
  rcases hc4 with h' | h' <;> rw [h'] at h <;> rcases h4 with h'' | h'' | h'' | h'' <;>
    rw [h''] at h <;> norm_num at h <;> omega

theorem eq_mul_of_dvd' (hprod : d₁ * d₂ = D * c ^ 2) {m : ℤ} (hm : d₁ = c * m) (hc0 : c ≠ 0) :
    m * d₂ = D * c := by
  have hc0' : (c : ℤ) ≠ 0 := by exact_mod_cast hc0
  apply mul_left_cancel₀ hc0'
  rw [← mul_assoc, ← hm, hprod]; ring

/-- `d₂` is squarefree (PROVED). -/
theorem squarefree_d₂ (hprod : d₁ * d₂ = D * c ^ 2) (hsq : Squarefree d₁) (hcd : (c : ℤ) ∣ d₁)
    (hcD : Nat.Coprime c D.natAbs) (hDsq : Squarefree D) (hc0 : c ≠ 0) : Squarefree d₂ := by
  have hD0 : D ≠ 0 := hDsq.ne_zero
  have hd₁0 : d₁ ≠ 0 := hsq.ne_zero
  have hc0' : (c : ℤ) ≠ 0 := by exact_mod_cast hc0
  have hd₂0 : d₂ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hprod
    exact mul_ne_zero hD0 (pow_ne_zero 2 hc0') hprod.symm
  obtain ⟨m, hm⟩ := hcd
  have hmd := eq_mul_of_dvd' hprod hm hc0
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hd₂0]
  intro q hq hqq
  have hqp : Prime q := hq.prime
  have hqD : q ∣ c → ¬ q ∣ D := by
    intro hqc hqD
    have h1 : q ∣ Int.gcd c D := Int.dvd_coe_gcd hqc hqD
    rw [Int.gcd, Int.natAbs_natCast, hcD, Nat.cast_one] at h1
    exact hqp.not_unit (isUnit_of_dvd_one h1)
  by_cases hqc : q ∣ (c : ℤ)
  · obtain ⟨c', hc'⟩ := hqc
    obtain ⟨t, ht⟩ := hqq
    have hc'0 : c' ≠ 0 := by rintro rfl; rw [mul_zero] at hc'; exact hc0' hc'
    have hq0 : q ≠ 0 := hqp.ne_zero
    -- `q m t = D c'`
    have key : q * m * t = D * c' := by
      have h := hmd
      rw [ht, hc'] at h
      apply mul_left_cancel₀ hq0
      linear_combination h
    have hqDc : q ∣ D * c' := ⟨m * t, by rw [← key]; ring⟩
    rcases hqp.dvd_or_dvd hqDc with h | h
    · exact hqD ⟨c', hc'⟩ h
    · obtain ⟨c'', hc''⟩ := h
      apply hq.not_isUnit
      apply hsq q
      exact ⟨c'' * m, by rw [hm, hc', hc'']; ring⟩
  · have hcop : IsCoprime (q * q) ((c : ℤ) ^ 2) := by
      have h1 : IsCoprime q (c : ℤ) := (Prime.coprime_iff_not_dvd hqp).mpr hqc
      exact (h1.pow_right (n := 2)).mul_left (h1.pow_right (n := 2))
    have hdvd : q * q ∣ D * (c : ℤ) ^ 2 := by
      rw [← hprod]; exact Dvd.dvd.mul_left hqq _
    have := hcop.dvd_of_dvd_mul_right hdvd
    exact hq.not_isUnit (hDsq q this)

variable {p : ℕ}

/-- A prime `p ∣ c` divides `d₁` and `d₂` (PROVED). -/
theorem dvd_both_of_dvd_c (hprod : d₁ * d₂ = D * c ^ 2) (hsq : Squarefree d₁)
    (hcd : (c : ℤ) ∣ d₁) (hc0 : c ≠ 0) (hp : p.Prime) (hpc : p ∣ c) :
    (p : ℤ) ∣ d₁ ∧ (p : ℤ) ∣ d₂ := by
  have hpc' : (p : ℤ) ∣ c := by exact_mod_cast hpc
  refine ⟨hpc'.trans hcd, ?_⟩
  obtain ⟨m, hm⟩ := hcd
  have hmd := eq_mul_of_dvd' hprod hm hc0
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h1 : (p : ℤ) ∣ m * d₂ := by rw [hmd]; exact Dvd.dvd.mul_left hpc' _
  rcases hpp.dvd_or_dvd h1 with h | h
  · exfalso
    apply hpp.not_unit
    apply hsq (p : ℤ)
    rw [hm]
    exact mul_dvd_mul hpc' h
  · exact h

/-- A prime `p ∤ c` divides at most one of `d₁, d₂` (PROVED). -/
theorem not_dvd_both (hprod : d₁ * d₂ = D * c ^ 2) (hDsq : Squarefree D) (hp : p.Prime)
    (hpc : ¬ p ∣ c) : ¬ ((p : ℤ) ∣ d₁ ∧ (p : ℤ) ∣ d₂) := by
  rintro ⟨h1, h2⟩
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpc' : ¬ (p : ℤ) ∣ c := by exact_mod_cast hpc
  have hcop : IsCoprime ((p : ℤ) * p) ((c : ℤ) ^ 2) := by
    have h := (Prime.coprime_iff_not_dvd hpp).mpr hpc'
    exact (h.pow_right (n := 2)).mul_left (h.pow_right (n := 2))
  have hdvd : (p : ℤ) * p ∣ D * (c : ℤ) ^ 2 := by rw [← hprod]; exact mul_dvd_mul h1 h2
  exact hpp.not_unit (hDsq _ (hcop.dvd_of_dvd_mul_right hdvd))

/-- For `p ∤ c`: `p` divides one of `d₁, d₂` iff `p ∣ D` (PROVED). -/
theorem dvd_one_iff (hprod : d₁ * d₂ = D * c ^ 2) (hp : p.Prime) (hpc : ¬ p ∣ c) :
    ((p : ℤ) ∣ d₁ ∨ (p : ℤ) ∣ d₂) ↔ (p : ℤ) ∣ D := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpc' : ¬ (p : ℤ) ∣ c := by exact_mod_cast hpc
  constructor
  · intro h
    have h1 : (p : ℤ) ∣ D * (c : ℤ) ^ 2 := by
      rw [← hprod]
      rcases h with h | h
      · exact Dvd.dvd.mul_right h _
      · exact Dvd.dvd.mul_left h _
    rcases hpp.dvd_or_dvd h1 with h | h
    · exact h
    · exact absurd (hpp.dvd_of_dvd_pow h) hpc'
  · intro h
    have h1 : (p : ℤ) ∣ d₁ * d₂ := by rw [hprod]; exact Dvd.dvd.mul_right h _
    exact hpp.dvd_or_dvd h1

theorem gcd_eq_one_of_not_dvd (hp : p.Prime) {d : ℤ} (hpd : ¬ (p : ℤ) ∣ d) :
    (p : ℤ).gcd (d.natAbs : ℤ) = 1 := by
  rw [Int.gcd_natCast_natCast]
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (by
    intro h; apply hpd; exact Int.natCast_dvd.mpr h)

/-- `χ_d(p²) = 1` for `p ∤ d` (PROVED). -/
theorem chiD_sq_prime (hp : p.Prime) {d : ℤ} (hpd : ¬ (p : ℤ) ∣ d) : chiD d (p ^ 2) = 1 := by
  unfold chiD
  push_cast
  exact jacobiSym.sq_one' (gcd_eq_one_of_not_dvd hp hpd)

/-- `χ_d(p) = ±1` for `p ∤ d` (PROVED). -/
theorem chiD_eq_one_or (hp : p.Prime) {d : ℤ} (hpd : ¬ (p : ℤ) ∣ d) :
    chiD d p = 1 ∨ chiD d p = -1 :=
  jacobiSym.eq_one_or_neg_one (gcd_eq_one_of_not_dvd hp hpd)

/-- `χ_{d₁}(p) χ_{d₂}(p) = χ_D(p)` for `p ∤ c` (PROVED). -/
theorem chiD_mul_chiD (hprod : d₁ * d₂ = D * c ^ 2) (hd₁0 : d₁ ≠ 0) (hd₂0 : d₂ ≠ 0)
    (hD0 : D ≠ 0) (hp : p.Prime) (hpc : ¬ p ∣ c) : chiD d₁ p * chiD d₂ p = chiD D p := by
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [Nat.cast_zero, zero_pow two_ne_zero, mul_zero] at hprod
    exact mul_ne_zero hd₁0 hd₂0 hprod
  unfold chiD
  rw [← jacobiSym.mul_right' _ (Int.natAbs_ne_zero.mpr hd₁0) (Int.natAbs_ne_zero.mpr hd₂0),
    ← Int.natAbs_mul, hprod, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast,
    jacobiSym.mul_right' _ (Int.natAbs_ne_zero.mpr hD0) (pow_ne_zero 2 hc0), pow_two,
    jacobiSym.mul_right' _ hc0 hc0]
  have h1 : ((p : ℕ) : ℤ).gcd (c : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpc
  have h2 := jacobiSym.sq_one (a := (p : ℤ)) (b := c) (by exact_mod_cast h1)
  rw [pow_two] at h2
  rw [h2, mul_one]

end

end ZInQ.Contrib.CloudB3RC53.GenusOdd
