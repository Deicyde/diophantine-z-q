import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.BigOperators.Associated

/-! # Coprime lifts of primitive residue pairs -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric4

/-- A residue pair with no common divisor with `N` lifts to a coprime integer pair. -/
theorem exists_isCoprime_lift (N : ℕ) (a b : ℤ) (h : Int.gcd (Int.gcd a b) N = 1) :
    ∃ c d : ℤ, IsCoprime c d ∧ (N : ℤ) ∣ c - a ∧ (N : ℤ) ∣ d - b := by
  by_cases ha : a = 0
  · subst ha
    refine ⟨N, b, ?_, by simp, by simp⟩
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    simp only [Int.gcd, Int.natAbs_zero, Nat.gcd_zero_left, Int.natAbs_natCast] at h ⊢
    exact h
  classical
  let S : Finset ℕ := (a.natAbs.primeFactors).filter fun p : ℕ => ¬ ((p : ℤ) ∣ b)
  let t : ℕ := ∏ p ∈ S, p
  refine ⟨a, b + t * N, ?_, by simp, ⟨t, by ring⟩⟩
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpa : p ∣ a.natAbs :=
    Int.natCast_dvd.mp ((Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_left _ _))
  have hpd' : (p : ℤ) ∣ b + t * N := (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_right _ _)
  by_cases hpb : (p : ℤ) ∣ b
  · have hpN : ¬ p ∣ N := by
      intro hpN
      have : p ∣ Int.gcd (Int.gcd a b) N :=
        Nat.dvd_gcd (Nat.dvd_gcd hpa (Int.natCast_dvd.mp hpb)) (by simpa using hpN)
      rw [h] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hpt : ¬ p ∣ t := by
      intro hpt
      obtain ⟨q, hq, hpq⟩ := Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) hpt
      have hqS := Finset.mem_filter.mp hq
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqS.1
      have : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq
      subst this
      exact hqS.2 hpb
    have htN : ¬ (p : ℤ) ∣ (t * N : ℕ) := by
      rw [Int.natCast_dvd_natCast]
      exact fun h' => ((Nat.Prime.dvd_mul hp).mp h').elim hpt hpN
    apply htN
    have := (dvd_sub hpd' hpb)
    simpa using this
  · have hpS : p ∈ S :=
      Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpa, by simpa using ha⟩, hpb⟩
    have hpt : (p : ℤ) ∣ (t : ℤ) * N :=
      (Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem _ hpS)).mul_right _
    exact hpb (by simpa using dvd_sub hpd' hpt)

#print axioms exists_isCoprime_lift

end WeierstrassCurve.ModelLevels.ModelGeneric4
