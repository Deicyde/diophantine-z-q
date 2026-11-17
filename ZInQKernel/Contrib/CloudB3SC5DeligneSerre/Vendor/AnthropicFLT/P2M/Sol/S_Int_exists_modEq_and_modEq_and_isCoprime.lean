/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Int_exists_modEq_and_modEq_and_isCoprime (git blob 5d49bc8516b9035950938733ac1549526bd7e235, sha256 2d56c19575eb1c98421976b17fe66dd5b5c653fb1b9607b740078f57ed1ae24b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_Int_exists_modEq_and_modEq_and_isCoprime

namespace M4aP1R
namespace UnimodularLift

theorem triple_of_modEq {n c d d' : ℤ} (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1)
    (hd : d' ≡ d [ZMOD n]) : ∃ x y z : ℤ, x * c + y * d' + z * n = 1 := by
  obtain ⟨x, y, z, hxyz⟩ := h

  obtain ⟨t, ht⟩ := (Int.modEq_iff_dvd.mp hd.symm)
  exact ⟨x, y, z - y * t, by linear_combination hxyz + y * ht⟩

theorem not_dvd_n_of_dvd {n c d p : ℤ} (hp : Prime p) (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1)
    (hpc : p ∣ c) (hpd : p ∣ d) : ¬ p ∣ n := by
  rintro hpn
  obtain ⟨x, y, z, hxyz⟩ := h
  have h1 : p ∣ (1 : ℤ) := by
    rw [← hxyz]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right hpc x) (dvd_mul_of_dvd_right hpd y))
      (dvd_mul_of_dvd_right hpn z)
  exact hp.not_unit (isUnit_of_dvd_one h1)

theorem exists_of_ne_zero {n c d : ℤ} (hd : d ≠ 0) (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1) :
    ∃ c' : ℤ, c' ≡ c [ZMOD n] ∧ IsCoprime c' d := by
  classical

  set S : Finset ℕ := d.natAbs.primeFactors.filter (fun p => ¬ (p : ℤ) ∣ c) with hS
  set m : ℤ := ∏ p ∈ S, (p : ℤ) with hm
  refine ⟨c + n * m, ?_, ?_⟩
  ·
    exact Int.modEq_iff_dvd.mpr ⟨-m, by ring⟩
  ·
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    change Nat.Coprime d.natAbs (c + n * m).natAbs
    refine Nat.Coprime.symm (Nat.coprime_of_dvd fun p hp hpc' hpd => ?_)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hpd' : (p : ℤ) ∣ d := Int.natCast_dvd.mpr hpd
    have hpc'Z : (p : ℤ) ∣ c + n * m := Int.natCast_dvd.mpr hpc'
    by_cases hpc : (p : ℤ) ∣ c
    ·
      have hpn : ¬ (p : ℤ) ∣ n := not_dvd_n_of_dvd hpZ h hpc hpd'
      have hpm : ¬ (p : ℤ) ∣ m := by
        rw [hm, hpZ.dvd_finsetProd_iff]
        rintro ⟨q, hq, hpq⟩
        rw [hS, Finset.mem_filter] at hq
        have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq.1
        have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp (Int.natCast_dvd_natCast.mp hpq)
        exact hq.2 (hpq' ▸ hpc)
      have hpnm : ¬ (p : ℤ) ∣ n * m := fun hnm => (hpZ.dvd_or_dvd hnm).elim hpn hpm
      have hnm : (p : ℤ) ∣ n * m := by
        have h2 := dvd_sub hpc'Z hpc
        rwa [add_sub_cancel_left] at h2
      exact hpnm hnm
    ·
      have hpS : p ∈ S := by
        rw [hS, Finset.mem_filter, Nat.mem_primeFactors]
        exact ⟨⟨hp, hpd, Int.natAbs_ne_zero.mpr hd⟩, hpc⟩
      have hpm : (p : ℤ) ∣ m := hm ▸ Finset.dvd_prod_of_mem _ hpS
      have : (p : ℤ) ∣ c := by
        have h2 : (p : ℤ) ∣ n * m := dvd_mul_of_dvd_right hpm n
        have h3 := dvd_sub hpc'Z h2
        rwa [add_sub_cancel_right] at h3
      exact hpc this

theorem exists_modEq_and_modEq_and_isCoprime_impl {n c d : ℤ}
    (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1) :
    ∃ c' d' : ℤ, c' ≡ c [ZMOD n] ∧ d' ≡ d [ZMOD n] ∧ IsCoprime c' d' := by
  by_cases hn : n = 0
  · subst hn
    obtain ⟨x, y, z, hxyz⟩ := h
    exact ⟨c, d, Int.ModEq.refl c, Int.ModEq.refl d, x, y, by linear_combination hxyz⟩

  obtain ⟨d', hd'd, hd'0⟩ : ∃ d' : ℤ, d' ≡ d [ZMOD n] ∧ d' ≠ 0 := by
    by_cases hd : d = 0
    · exact ⟨n, by rw [hd]; exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩, hn⟩
    · exact ⟨d, Int.ModEq.refl d, hd⟩
  obtain ⟨c', hc'c, hcop⟩ := exists_of_ne_zero hd'0 (triple_of_modEq h hd'd)
  exact ⟨c', d', hc'c, hd'd, hcop⟩

end M4aP1R.UnimodularLift

theorem solution {n c d : ℤ}
    (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1) :
    ∃ c' d' : ℤ, c' ≡ c [ZMOD n] ∧ d' ≡ d [ZMOD n] ∧ IsCoprime c' d' := by
  first
    | exact M4aP1R.UnimodularLift.exists_modEq_and_modEq_and_isCoprime_impl h
    | (apply M4aP1R.UnimodularLift.exists_modEq_and_modEq_and_isCoprime_impl <;> assumption)
