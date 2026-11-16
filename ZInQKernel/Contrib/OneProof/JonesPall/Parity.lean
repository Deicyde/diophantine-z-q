import ZInQKernel.Contrib.OneProof.JonesPall.Quaternion

/-! Kernel-checked residue facts for the Jones–Pall squarefree specialization. -/

namespace ZInQ.Contrib.OneProof.JonesPall

open scoped Quaternion

/-- An integer represented by three squares and congruent to 1 modulo 4 has
exactly one odd coordinate. -/
theorem one_odd_of_sum_three_sq {a b c : ℤ}
    (h : (a ^ 2 + b ^ 2 + c ^ 2) % 4 = 1) :
    (a % 2 = 1 ∧ b % 2 = 0 ∧ c % 2 = 0) ∨
    (b % 2 = 1 ∧ c % 2 = 0 ∧ a % 2 = 0) ∨
    (c % 2 = 1 ∧ a % 2 = 0 ∧ b % 2 = 0) := by
  have ha0 := Int.emod_nonneg a (by decide : (4 : ℤ) ≠ 0)
  have ha4 := Int.emod_lt_of_pos a (by decide : (0 : ℤ) < 4)
  have hb0 := Int.emod_nonneg b (by decide : (4 : ℤ) ≠ 0)
  have hb4 := Int.emod_lt_of_pos b (by decide : (0 : ℤ) < 4)
  have hc0 := Int.emod_nonneg c (by decide : (4 : ℤ) ≠ 0)
  have hc4 := Int.emod_lt_of_pos c (by decide : (0 : ℤ) < 4)
  have hh : ((a % 4) ^ 2 + (b % 4) ^ 2 + (c % 4) ^ 2) % 4 = 1 := by
    have he := (((Int.mod_modEq a 4).pow 2).add ((Int.mod_modEq b 4).pow 2)).add
      ((Int.mod_modEq c 4).pow 2)
    change ((a % 4) ^ 2 + (b % 4) ^ 2 + (c % 4) ^ 2) % 4 =
      (a ^ 2 + b ^ 2 + c ^ 2) % 4 at he
    exact he.trans h
  interval_cases haR : a % 4 <;> interval_cases hbR : b % 4 <;> interval_cases hcR : c % 4 <;>
    norm_num at hh <;> omega

/-- In the oriented 1-mod-8 case, the two even coordinates are either both
multiples of four, or both 2 modulo four. -/
theorem even_coordinate_patterns {a b c : ℤ}
    (h : (a ^ 2 + b ^ 2 + c ^ 2) % 8 = 1)
    (ha : a % 2 = 1) (hb : b % 2 = 0) (hc : c % 2 = 0) :
    (b % 4 = 0 ∧ c % 4 = 0) ∨ (b % 4 = 2 ∧ c % 4 = 2) := by
  have ha0 := Int.emod_nonneg a (by decide : (8 : ℤ) ≠ 0)
  have ha8 := Int.emod_lt_of_pos a (by decide : (0 : ℤ) < 8)
  have hb0 := Int.emod_nonneg b (by decide : (8 : ℤ) ≠ 0)
  have hb8 := Int.emod_lt_of_pos b (by decide : (0 : ℤ) < 8)
  have hc0 := Int.emod_nonneg c (by decide : (8 : ℤ) ≠ 0)
  have hc8 := Int.emod_lt_of_pos c (by decide : (0 : ℤ) < 8)
  have hh : ((a % 8) ^ 2 + (b % 8) ^ 2 + (c % 8) ^ 2) % 8 = 1 := by
    have he := (((Int.mod_modEq a 8).pow 2).add ((Int.mod_modEq b 8).pow 2)).add
      ((Int.mod_modEq c 8).pow 2)
    change ((a % 8) ^ 2 + (b % 8) ^ 2 + (c % 8) ^ 2) % 8 =
      (a ^ 2 + b ^ 2 + c ^ 2) % 8 at he
    exact he.trans h
  interval_cases haR : a % 8 <;> interval_cases hbR : b % 8 <;> interval_cases hcR : c % 8 <;>
    norm_num at hh <;> omega

/-- Conjugation by a quaternion of norm 3 modulo 4 switches an oriented bad
three-square residue pattern to one with both even coordinates 0 modulo 4. -/
theorem conjugation_bad_pattern {q : Q} {a b c : ℤ}
    (hN : Quaternion.normSq q % 4 = 3) (ha : a % 2 = 1)
    (hb : b % 4 = 2) (hc : c % 4 = 2) :
    (4 : ℤ) ∣ ((q * (⟨0, a, b, c⟩ : Q)) * star q).imJ ∧
    (4 : ℤ) ∣ ((q * (⟨0, a, b, c⟩ : Q)) * star q).imK := by
  have table : ∀ t0 t1 t2 t3 x : ZMod 4,
      t0 ^ 2 + t1 ^ 2 + t2 ^ 2 + t3 ^ 2 = 3 → (x = 1 ∨ x = 3) →
      let t : Quaternion (ZMod 4) := ⟨t0, t1, t2, t3⟩
      ((t * (⟨0, x, 2, 2⟩ : Quaternion (ZMod 4))) * star t).imJ = 0 ∧
      ((t * (⟨0, x, 2, 2⟩ : Quaternion (ZMod 4))) * star t).imK = 0 := by
    decide
  have hq : (q.re : ZMod 4) ^ 2 + (q.imI : ZMod 4) ^ 2 +
      (q.imJ : ZMod 4) ^ 2 + (q.imK : ZMod 4) ^ 2 = 3 := by
    have hcast : ((Quaternion.normSq q : ℤ) : ZMod 4) = 3 := by
      exact (ZMod.intCast_eq_intCast_iff' (Quaternion.normSq q : ℤ) 3 4).mpr
        (by simpa using hN)
    simpa only [Quaternion.normSq_def', Int.cast_add, Int.cast_pow] using hcast
  have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have hxa : (a : ZMod 4) = 1 ∨ (a : ZMod 4) = 3 := by
    rcases ha4 with h1 | h3
    · left
      exact (ZMod.intCast_eq_intCast_iff' a 1 4).mpr (by simpa using h1)
    · right
      exact (ZMod.intCast_eq_intCast_iff' a 3 4).mpr (by simpa using h3)
  have hxb : (b : ZMod 4) = 2 :=
    (ZMod.intCast_eq_intCast_iff' b 2 4).mpr (by simpa using hb)
  have hxc : (c : ZMod 4) = 2 :=
    (ZMod.intCast_eq_intCast_iff' c 2 4).mpr (by simpa using hc)
  have ht := table (q.re : ZMod 4) (q.imI : ZMod 4) (q.imJ : ZMod 4)
    (q.imK : ZMod 4) (a : ZMod 4) hq hxa
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (((q * (⟨0, a, b, c⟩ : Q)) * star q).imJ) 4).mp
    simpa [Quaternion.imJ_mul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg, hxb, hxc]
      using ht.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (((q * (⟨0, a, b, c⟩ : Q)) * star q).imK) 4).mp
    simpa [Quaternion.imJ_mul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg, hxb, hxc]
      using ht.2

end ZInQ.Contrib.OneProof.JonesPall
