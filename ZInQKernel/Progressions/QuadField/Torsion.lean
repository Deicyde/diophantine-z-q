/-
Plan step 3.2: a quadratic field has at most 6 roots of unity.
-/
import ZInQKernel.Progressions.QuadField.Basic

namespace ZInQ.Progressions

open NumberField NumberField.Units

/-- `φ(n) ≤ 2` forces `n ∣ 12` (for `n > 0`). -/
theorem dvd_twelve_of_totient_le_two :
    ∀ n : ℕ, 0 < n → n.totient ≤ 2 → n ∣ 12 := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _ h
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.totient_prime_pow_succ hp] at h
    have hp2 := hp.two_le
    have hp3 : p ≤ 3 := by
      have : p - 1 ≤ 2 := le_trans (Nat.le_mul_of_pos_left _ (by positivity)) h
      omega
    interval_cases p
    · have hk : 2 ^ k ≤ 2 := by simpa using h
      have : k ≤ 1 := by
        by_contra hk'
        have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases k <;> norm_num
    · have hk : 3 ^ k ≤ 1 := by
        have : 3 ^ k * 2 ≤ 2 := h
        omega
      have : k = 0 := by
        by_contra hk'
        have : 3 ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst this
      norm_num
  | zero => intro h; omega
  | one => intro _ _; exact one_dvd _
  | coprime a b ha hb hab iha ihb =>
    intro _ h
    rw [Nat.totient_mul hab] at h
    have hta : 0 < a.totient := Nat.totient_pos.mpr (by omega)
    have htb : 0 < b.totient := Nat.totient_pos.mpr (by omega)
    have h1 : a.totient ≤ 2 := le_trans (Nat.le_mul_of_pos_right _ htb) h
    have h2 : b.totient ≤ 2 := le_trans (Nat.le_mul_of_pos_left _ hta) h
    exact hab.mul_dvd_of_dvd_of_dvd (iha (by omega) h1) (ihb (by omega) h2)

/-- `φ(n) ≤ 2` forces `n ≤ 6`. -/
theorem le_six_of_totient_le_two {n : ℕ} (h : n.totient ≤ 2) : n ≤ 6 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  have h12 := dvd_twelve_of_totient_le_two n hn h
  have hle : n ≤ 12 := Nat.le_of_dvd (by norm_num) h12
  by_contra hgt
  interval_cases n <;> first | omega | (revert h; decide)

/-- A number field of degree 2 contains at most 6 roots of unity. -/
theorem torsionOrder_le_six_of_finrank_eq_two {K : Type*} [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 2) : torsionOrder K ≤ 6 := by
  obtain ⟨μ, hμ⟩ : ∃ μ : torsion K, orderOf μ = torsionOrder K :=
    IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  replace hμ := hμ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have key := IsPrimitiveRoot.lcm_totient_le_finrank hμ hμ
    (Polynomial.cyclotomic.irreducible_rat (by rw [Nat.lcm_self]; exact torsionOrder_pos K))
  rw [Nat.lcm_self, h] at key
  exact le_six_of_totient_le_two key

variable {d : ℤ} [Fact (¬ IsSquare (d : ℚ))]

/-- `ℚ(√d)` contains at most 6 roots of unity. -/
theorem Qsqrt.torsionOrder_le_six : torsionOrder (Qsqrt d) ≤ 6 :=
  torsionOrder_le_six_of_finrank_eq_two Qsqrt.finrank

end ZInQ.Progressions
