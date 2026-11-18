import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The norm calculation underlying the division prime (tex 8462–8463,
8551–8559). The explicit local calculation is provenance (c). -/

namespace ZInQ.Manuscript.RC.LocalDivision

variable {p : ℕ} [Fact p.Prime]

theorem neg_one_nonsquare (hp : p % 4 = 3) : ¬ IsSquare (-1 : ZMod p) := by
  rw [← quadraticChar_neg_one_iff_not_isSquare,
    quadraticChar_neg_one ((ringChar.eq (ZMod p) p).substr (by omega : p ≠ 2)),
    ZMod.card, ZMod.χ₄_nat_three_mod_four hp]

theorem residue_sum_sq_eq_zero (hp : p % 4 = 3) (a b : ZMod p) :
    a ^ 2 + b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    by_cases hb : b = 0
    · subst b
      simpa using h
    · exfalso
      apply neg_one_nonsquare hp
      refine ⟨a / b, ?_⟩
      rw [← sq, div_pow, eq_comm, div_eq_iff (pow_ne_zero _ hb)]
      linear_combination h
  · rintro ⟨rfl, rfl⟩
    simp

theorem padic_red_eq_zero_iff (a : ℤ_[p]) : PadicInt.toZMod a = 0 ↔ ‖a‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
  exact PadicInt.mem_nonunits

private theorem norm_one_add_sq (hp : p % 4 = 3) {a : ℚ_[p]} (ha : ‖a‖ ≤ 1) :
    ‖1 + a ^ 2‖ = 1 := by
  let b : ℤ_[p] := ⟨a, ha⟩
  have h : PadicInt.toZMod (1 + b ^ 2) ≠ 0 := by
    intro hz
    simp only [map_add, map_one, map_pow] at hz
    exact one_ne_zero ((residue_sum_sq_eq_zero hp 1 _).mp (by simpa only [one_pow] using hz)).1
  change ‖(1 + b ^ 2 : ℤ_[p])‖ = 1
  exact le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp (mt (padic_red_eq_zero_iff (1 + b ^ 2)).mpr h))

private theorem norm_pair_of_le (hp : p % 4 = 3) (a b : ℚ_[p]) (hab : ‖b‖ ≤ ‖a‖) :
    ‖a ^ 2 + b ^ 2‖ = ‖a‖ ^ 2 := by
  by_cases ha : a = 0
  · have hb : b = 0 := norm_le_zero_iff.mp (by simpa [ha] using hab)
    simp [ha, hb]
  · have hc : ‖b / a‖ ≤ 1 := by rw [norm_div, div_le_one (norm_pos_iff.mpr ha)]; exact hab
    have he : a ^ 2 + b ^ 2 = a ^ 2 * (1 + (b / a) ^ 2) := by field_simp
    rw [he, norm_mul, norm_one_add_sq hp hc, mul_one, norm_pow]

theorem norm_pair (hp : p % 4 = 3) (a b : ℚ_[p]) :
    ‖a ^ 2 + b ^ 2‖ = max ‖a‖ ‖b‖ ^ 2 := by
  rcases le_total ‖b‖ ‖a‖ with h | h
  · rw [max_eq_left h, norm_pair_of_le hp _ _ h]
  · rw [max_eq_right h, add_comm, norm_pair_of_le hp _ _ h]

theorem valuation_pair_even (hp : p % 4 = 3) (a b : ℚ_[p]) :
    ∃ k : ℤ, (a ^ 2 + b ^ 2).valuation = 2 * k := by
  have aux (a b : ℚ_[p]) (h : ‖b‖ ≤ ‖a‖) (hs : a ^ 2 + b ^ 2 ≠ 0) :
      (a ^ 2 + b ^ 2).valuation = 2 * a.valuation := by
    have ha : a ≠ 0 := by
      intro he
      have hz := norm_pair_of_le hp a b h
      exact hs (norm_eq_zero.mp (hz.trans (by simp [he])))
    have hn := norm_pair_of_le hp a b h
    rw [Padic.norm_eq_zpow_neg_valuation hs, ← norm_pow, Padic.norm_eq_zpow_neg_valuation
      (pow_ne_zero 2 ha), Padic.valuation_pow] at hn
    have hbase : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have := zpow_right_injective₀ (zero_lt_one.trans hbase) hbase.ne' hn
    omega
  by_cases h : a ^ 2 + b ^ 2 = 0
  · exact ⟨0, by simp [h]⟩
  rcases le_total ‖b‖ ‖a‖ with hab | hab
  · exact ⟨_, aux a b hab h⟩
  · rw [add_comm] at h ⊢
    exact ⟨_, aux b a hab h⟩

theorem norm_four (hp : p % 4 = 3) (a b c d : ℚ_[p]) :
    ‖a ^ 2 + b ^ 2 + (p : ℚ_[p]) * (c ^ 2 + d ^ 2)‖ =
      max (max ‖a‖ ‖b‖ ^ 2) (‖(p : ℚ_[p])‖ * max ‖c‖ ‖d‖ ^ 2) := by
  suffices h : ‖a ^ 2 + b ^ 2 + (p : ℚ_[p]) * (c ^ 2 + d ^ 2)‖ =
      max ‖a ^ 2 + b ^ 2‖ ‖(p : ℚ_[p]) * (c ^ 2 + d ^ 2)‖ by
    rw [h, norm_mul, norm_pair hp, norm_pair hp]
  by_cases ha : a ^ 2 + b ^ 2 = 0
  · rw [ha, zero_add, norm_zero, max_eq_right (norm_nonneg _)]
  by_cases hc : c ^ 2 + d ^ 2 = 0
  · rw [hc, mul_zero, add_zero, norm_zero, max_eq_left (norm_nonneg _)]
  have hpn : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply Padic.add_eq_max_of_ne
  intro h
  rw [Padic.norm_eq_zpow_neg_valuation ha, Padic.norm_eq_zpow_neg_valuation (mul_ne_zero hpn hc),
    Padic.valuation_mul hpn hc, Padic.valuation_p] at h
  have hbase : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have he := zpow_right_injective₀ (zero_lt_one.trans hbase) hbase.ne' h
  obtain ⟨k, hk⟩ := valuation_pair_even hp a b
  obtain ⟨l, hl⟩ := valuation_pair_even hp c d
  omega

#print axioms neg_one_nonsquare
#print axioms residue_sum_sq_eq_zero
#print axioms padic_red_eq_zero_iff
#print axioms norm_one_add_sq
#print axioms norm_pair_of_le
#print axioms norm_pair
#print axioms valuation_pair_even
#print axioms norm_four

end ZInQ.Manuscript.RC.LocalDivision
