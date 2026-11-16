import ZInQKernel.Contrib.OneProof.LegendreThreeSquares.Atlas
import ZInQKernel.Contrib.OneProof.JonesPall.Descent
import ZInQKernel.Contrib.OneProof.JonesPall.Parity
import Mathlib.NumberTheory.SumTwoSquares

/-!
# The squarefree 1-mod-8 representation by x²+y²+16z²

This uses the unchanged genuine Atlas/Ankeny three-square proof, Mathlib's
sum-of-two-squares criterion, and the integral quaternion descent proved in
this contribution. It takes neither Legendre nor Jones–Pall as an assumption.
-/

namespace ZInQ.Contrib.OneProof.JonesPall

open scoped Quaternion

private theorem oriented_three_squares (n : ℕ) (hn : n % 8 = 1) :
    ∃ a b c : ℤ, (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 ∧
      a % 2 = 1 ∧ b % 2 = 0 ∧ c % 2 = 0 := by
  have hnot : ¬ ∃ u v : ℕ, n = 4 ^ u * (8 * v + 7) := by
    rintro ⟨u, v, heq⟩
    rcases u with _ | u
    · simp only [pow_zero, one_mul] at heq
      omega
    · have htwo : 2 ∣ n :=
        ⟨2 * 4 ^ u * (8 * v + 7), by rw [heq, pow_succ]; ring⟩
      omega
  obtain ⟨x, y, z, hxyz⟩ :=
    ZInQ.Contrib.OneProof.LegendreThreeSquares.Atlas.Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven n hnot
  have h : (n : ℤ) = (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 := by
    exact_mod_cast hxyz.symm
  have hn4 : n % 4 = 1 := by omega
  have hm : ((x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2) % 4 = 1 := by
    rw [← h]
    exact_mod_cast hn4
  rcases one_odd_of_sum_three_sq hm with h1 | h2 | h3
  · exact ⟨x, y, z, h, h1⟩
  · refine ⟨y, z, x, ?_, h2⟩
    simpa only [add_comm, add_left_comm, add_assoc] using h
  · refine ⟨z, x, y, ?_, h3⟩
    simpa only [add_comm, add_left_comm, add_assoc] using h

private theorem pure_not_dvd_prime {n p : ℕ} (hn : Squarefree n) (hp : p.Prime)
    {a b c : ℤ} (h : (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2) :
    ¬ DvdQ p (⟨0, a, b, c⟩ : Q) := by
  intro hdiv
  obtain ⟨a', ha⟩ := hdiv.2.1
  obtain ⟨b', hb⟩ := hdiv.2.2.1
  obtain ⟨c', hc⟩ := hdiv.2.2.2
  change a = (p : ℤ) * a' at ha
  change b = (p : ℤ) * b' at hb
  change c = (p : ℤ) * c' at hc
  have hd : (p : ℤ) ^ 2 ∣ (n : ℤ) := by
    refine ⟨a' ^ 2 + b' ^ 2 + c' ^ 2, ?_⟩
    rw [h, ha, hb, hc]
    ring
  have hdInt : (p : ℤ) * (p : ℤ) ∣ (n : ℤ) := by
    simpa only [pow_two] using hd
  have hdNat : p * p ∣ n := by
    exact_mod_cast hdInt
  exact hp.not_isUnit (hn p hdNat)

private theorem conjugation_re_zero (q v : Q) (hv : v.re = 0) :
    ((q * v) * star q).re = 0 := by
  have hvstar : star v = -v := Quaternion.star_eq_neg.mpr hv
  have hs : star ((q * v) * star q) = -((q * v) * star q) := by
    simp only [star_mul, star_star, hvstar, neg_mul, mul_neg, mul_assoc]
  have hr := congrArg (fun t : Q => t.re) hs
  simp only [Quaternion.re_star, Quaternion.re_neg] at hr
  omega

private theorem divide_odd_preserves_four {p u x : ℤ} (hp : p % 4 = 3)
    (heq : p * x = u) (hu : (4 : ℤ) ∣ u) : (4 : ℤ) ∣ x := by
  have hu0 : u % 4 = 0 := by obtain ⟨s, hs⟩ := hu; omega
  have hmod := congrArg (fun y : ℤ => y % 4) heq
  rw [Int.mul_emod, hp, hu0] at hmod
  have hx0 : x % 4 = 0 := by omega
  exact ⟨x / 4, by omega⟩

/-- The exact general representation; no bounded computation or additional
outer representation hypothesis is used. -/
theorem jonesPall_representation :
    ∀ n : ℕ, Squarefree n → n % 8 = 1 →
      ∃ x y z : ℤ, (n : ℤ) = x ^ 2 + y ^ 2 + 16 * z ^ 2 := by
  intro n hsq hn
  by_cases hAll : ∀ p ∈ n.primeFactors, p % 4 ≠ 3
  · have hneg := (ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three hsq).mpr hAll
    obtain ⟨x, y, hxy⟩ := Nat.eq_sq_add_sq_of_isSquare_mod_neg_one hneg
    refine ⟨x, y, 0, ?_⟩
    simpa using (show (n : ℤ) = (x : ℤ) ^ 2 + (y : ℤ) ^ 2 by exact_mod_cast hxy)
  · push Not at hAll
    obtain ⟨p, hpf, hp4⟩ := hAll
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpf
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpf
    have hp2 : p ≠ 2 := by omega
    have hpZ0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpZ4 : (p : ℤ) % 4 = 3 := by exact_mod_cast hp4
    obtain ⟨a, b, c, hN, ha, hb, hc⟩ := oriented_three_squares n hn
    have h8 : (a ^ 2 + b ^ 2 + c ^ 2) % 8 = 1 := by rw [← hN]; exact_mod_cast hn
    rcases even_coordinate_patterns h8 ha hb hc with hgood | hbad
    · have he : c = 4 * (c / 4) := by omega
      have hs : c ^ 2 = 16 * (c / 4) ^ 2 := by
        calc c ^ 2 = (4 * (c / 4)) ^ 2 := congrArg (fun x : ℤ => x ^ 2) he
             _ = 16 * (c / 4) ^ 2 := by ring
      exact ⟨a, b, c / 4, by simpa only [hs] using hN⟩
    · let v : Q := ⟨0, a, b, c⟩
      have hNv : Quaternion.normSq v = (n : ℤ) := by
        simpa only [v, Quaternion.normSq_def', zero_pow two_ne_zero, zero_add] using hN.symm
      have hv : ¬ DvdQ p v := pure_not_dvd_prime hsq hp hN
      have hpnZ : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hpn
      have hvv : DvdQ p (v * v) := by
        have hs : v * v = (-(n : ℤ) : Q) := by
          apply Quaternion.ext <;> simp [v] <;> nlinarith [hN]
        rw [hs]
        exact dvdQ_coe (dvd_neg.mpr hpnZ)
      obtain ⟨q, hNq, hIq⟩ := exists_norm_prime_annihilator p hp hp2 v hv hvv (by rwa [hNv])
      let u := (q * v) * star q
      have hu : DvdQ p u := dvdQ_mul_right hIq (star q)
      let w := divQ p u
      have hNw : Quaternion.normSq w = (n : ℤ) := by
        have h := normSq_divQ hu
        change (p : ℤ) ^ 2 * Quaternion.normSq w = Quaternion.normSq ((q * v) * star q) at h
        rw [map_mul, map_mul, Quaternion.normSq_star, hNq, hNv] at h
        apply mul_left_cancel₀ (pow_ne_zero 2 hpZ0)
        calc (p : ℤ) ^ 2 * Quaternion.normSq w = ((p : ℤ) * n) * p := h
             _ = (p : ℤ) ^ 2 * (n : ℤ) := by ring
      have hure : u.re = 0 := conjugation_re_zero q v rfl
      have hwre : w.re = 0 := by simp only [w, divQ, hure, Int.zero_ediv]
      have hQ4 : Quaternion.normSq q % 4 = 3 := by rw [hNq]; exact hpZ4
      have h4 := conjugation_bad_pattern hQ4 ha hbad.1 hbad.2
      have hc4 : (4 : ℤ) ∣ w.imK := by
        apply divide_odd_preserves_four hpZ4 (u := u.imK)
        · exact Int.mul_ediv_cancel' hu.2.2.2
        · exact h4.2
      obtain ⟨z, hz⟩ := hc4
      refine ⟨w.imI, w.imJ, z, ?_⟩
      rw [Quaternion.normSq_def', hwre, zero_pow two_ne_zero, zero_add] at hNw
      rw [hz] at hNw
      nlinarith

end ZInQ.Contrib.OneProof.JonesPall
