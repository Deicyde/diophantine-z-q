import Mathlib

/-!
# mcheck-22p step 4: tex L948-954, `h(u) ≤ h(j) + log(2·4000⁶)`

`j = a/b = J(u) = -57600 F(u)² / G(u)⁶` with `u = p/q` in lowest terms. Clearing `q¹²` turns
`b·(-57600 F(u)²) = a·G(u)⁶` into the homogeneous equation `heq` below. The rational-root
argument of the manuscript (numerator ∣ constant coefficient `-a·3600⁶`, denominator ∣ highest
nonzero coefficient) gives `max(|p|, q) ≤ 2·4000⁶·max(|a|, b)`; here it is proved directly.
The case where the leading coefficient `-57600 b - 7⁶ a` vanishes (`j = -57600/117649`) is the
"use the actual highest nonzero coefficient" clause of tex L951-952.
-/

namespace MCheck22P.L954

def Fh (p q : ℤ) : ℤ := p * (p + 15 * q) * (p + 20 * q) * (p + 24 * q) * (p + 30 * q) * (p + 60 * q)
def Gh (p q : ℤ) : ℤ := 7 * p ^ 2 + 300 * p * q + 3600 * q ^ 2

theorem bound_p {p q a b : ℤ} (hpq : IsCoprime p q) (ha : a ≠ 0)
    (heq : -57600 * b * Fh p q ^ 2 = a * Gh p q ^ 6) : p.natAbs ≤ 3600 ^ 6 * a.natAbs := by
  have hpF : p ∣ Fh p q := ⟨(p + 15 * q) * (p + 20 * q) * (p + 24 * q) * (p + 30 * q) *
    (p + 60 * q), by unfold Fh; ring⟩
  have h1 : p ∣ a * Gh p q ^ 6 := by
    rw [← heq]; exact Dvd.dvd.mul_left (dvd_pow hpF two_ne_zero) _
  have hG : Gh p q ≡ 3600 * q ^ 2 [ZMOD p] := by
    have : Gh p q = 3600 * q ^ 2 + p * (7 * p + 300 * q) := by unfold Gh; ring
    rw [this]; exact (Int.modEq_iff_dvd.2 ⟨-(7 * p + 300 * q), by ring⟩)
  have h2 : p ∣ a * (3600 * q ^ 2) ^ 6 := by
    have := Int.ModEq.dvd ((hG.pow 6).mul_left a)
    have h := dvd_add this h1
    rwa [sub_add_cancel] at h
  have h3 : p ∣ a * 3600 ^ 6 := by
    have hc : IsCoprime p (q ^ 12) := hpq.pow_right
    have : a * (3600 * q ^ 2) ^ 6 = (a * 3600 ^ 6) * q ^ 12 := by ring
    rw [this] at h2; exact hc.dvd_of_dvd_mul_right h2
  have hne : a * 3600 ^ 6 ≠ 0 := mul_ne_zero ha (by norm_num)
  have := Int.natAbs_le_of_dvd_ne_zero h3 hne
  simpa [Int.natAbs_mul, mul_comm] using this

theorem bound_q {p q a b : ℤ} (hq : 0 < q) (hpq : IsCoprime p q) (hb : 0 < b)
    (hab : IsCoprime a b) (heq : -57600 * b * Fh p q ^ 2 = a * Gh p q ^ 6) :
    q.natAbs ≤ 57600 * b.natAbs + 117649 * a.natAbs := by
  have hF : Fh p q ≡ p ^ 6 [ZMOD q] := by
    have h : ∀ c : ℤ, p + c * q ≡ p [ZMOD q] := fun c =>
      Int.modEq_iff_dvd.2 ⟨-c, by ring⟩
    have := (((((Int.ModEq.refl p).mul (h 15)).mul (h 20)).mul (h 24)).mul (h 30)).mul (h 60)
    unfold Fh; convert this using 1; ring
  have hG : Gh p q ≡ 7 * p ^ 2 [ZMOD q] := by
    have : Gh p q = 7 * p ^ 2 + q * (300 * p + 3600 * q) := by unfold Gh; ring
    rw [this]; exact Int.modEq_iff_dvd.2 ⟨-(300 * p + 3600 * q), by ring⟩
  have hE : (0 : ℤ) ≡ p ^ 12 * -(57600 * b + 117649 * a) [ZMOD q] := by
    have h0 : (0 : ℤ) = -57600 * b * Fh p q ^ 2 - a * Gh p q ^ 6 := by rw [heq]; ring
    have := (((hF.pow 2).mul_left (-57600 * b)).sub ((hG.pow 6).mul_left a))
    rw [← h0] at this; convert this using 1; ring
  have hd : q ∣ p ^ 12 * (57600 * b + 117649 * a) := by
    have := (Int.modEq_iff_dvd.1 hE)
    rw [show p ^ 12 * -(57600 * b + 117649 * a) - 0 = -(p ^ 12 * (57600 * b + 117649 * a)) by
      ring] at this
    exact (dvd_neg).1 this
  have hd2 : q ∣ 57600 * b + 117649 * a := (hpq.symm.pow_right (n := 12)).dvd_of_dvd_mul_left hd
  rcases eq_or_ne (57600 * b + 117649 * a) 0 with hz | hz
  · -- `j = -57600/117649`: then `b = 117649`, `a = -57600` and `q ∣ 7007` or `q ∣ 686`
    have hb' : b ∣ 117649 := by
      have : b ∣ 117649 * a := ⟨-57600, by linarith⟩
      exact hab.symm.dvd_of_dvd_mul_right this
    have ha' : a ∣ 57600 := by
      have : a ∣ 57600 * b := ⟨-117649, by linarith⟩
      exact hab.dvd_of_dvd_mul_right this
    have hb1 : 1 ≤ b.natAbs := by omega
    -- 117649 F² = G⁶
    have hsq : (343 * Fh p q) ^ 2 = (Gh p q ^ 3) ^ 2 := by
      have hbne : b ≠ 0 := hb.ne'
      have : 117649 * a = -57600 * b := by linarith
      have h2 := congrArg (fun t => 117649 * t) heq
      have : -57600 * b * (117649 * Fh p q ^ 2) = -57600 * b * (Gh p q ^ 6) := by
        linear_combination h2 + Gh p q ^ 6 * this
      have := mul_left_cancel₀ (mul_ne_zero (by norm_num) hbne) this
      linear_combination this
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).symm with h | h
    · -- 343 F = -G³:  G³ + 343 F = 686 p⁶ + q(95207 p⁵ + q R)
      have hid : Gh p q ^ 3 + 343 * Fh p q = 686 * p ^ 6 + q * (95207 * p ^ 5 + q *
          (5248950 * p ^ 4 + 146448000 * p ^ 3 * q + 2170260000 * p ^ 2 * q ^ 2 +
            16109280000 * p * q ^ 3 + 46656000000 * q ^ 4)) := by unfold Gh Fh; ring
      have : q ∣ 686 * p ^ 6 := by
        refine ⟨-(95207 * p ^ 5 + q * (5248950 * p ^ 4 + 146448000 * p ^ 3 * q +
          2170260000 * p ^ 2 * q ^ 2 + 16109280000 * p * q ^ 3 + 46656000000 * q ^ 4)), ?_⟩
        linear_combination (-1 : ℤ) * hid + h
      have : q ∣ 686 := (hpq.symm.pow_right (n := 6)).dvd_of_dvd_mul_right this
      have := Int.natAbs_le_of_dvd_ne_zero this (by norm_num)
      simp at this; omega
    · -- 343 F = G³:  G³ - 343 F = q(-7007 p⁵ + q R)
      have hid : Gh p q ^ 3 - 343 * Fh p q = q * (-7007 * p ^ 5 + q *
          (-410550 * p ^ 4 - 1728000 * p ^ 3 * q + 318060000 * p ^ 2 * q ^ 2 +
            7218720000 * p * q ^ 3 + 46656000000 * q ^ 4)) := by unfold Gh Fh; ring
      have hz' : q * (-7007 * p ^ 5 + q * (-410550 * p ^ 4 - 1728000 * p ^ 3 * q +
          318060000 * p ^ 2 * q ^ 2 + 7218720000 * p * q ^ 3 + 46656000000 * q ^ 4)) = 0 := by
        rw [← hid]; linear_combination -h
      have hz'' := (mul_eq_zero.1 hz').resolve_left hq.ne'
      have : q ∣ 7007 * p ^ 5 := ⟨-410550 * p ^ 4 - 1728000 * p ^ 3 * q +
          318060000 * p ^ 2 * q ^ 2 + 7218720000 * p * q ^ 3 + 46656000000 * q ^ 4, by
        linear_combination -hz''⟩
      have : q ∣ 7007 := (hpq.symm.pow_right (n := 5)).dvd_of_dvd_mul_right this
      have := Int.natAbs_le_of_dvd_ne_zero this (by norm_num)
      simp at this; omega
  · have := Int.natAbs_le_of_dvd_ne_zero hd2 hz
    have h' : (57600 * b + 117649 * a).natAbs ≤ 57600 * b.natAbs + 117649 * a.natAbs := by
      have := Int.natAbs_add_le (57600 * b) (117649 * a)
      simpa [Int.natAbs_mul] using this
    omega

/-- **tex L948-954.** With `u = p/q` (lowest terms, `q > 0`) and `j = a/b` (lowest terms,
`b > 0`, `j ≠ 0`) related by `j = J(u)`, both `|p|` and `q` are at most `2·4000⁶·max(|a|, b)`;
so `H(u) ≤ 2·4000⁶ H(j)`, i.e. `h(u) ≤ h(j) + log(2·4000⁶)`, and `log(2·4000⁶) < 74`. -/
theorem height_bound {p q a b : ℤ} (hq : 0 < q) (hpq : IsCoprime p q) (hb : 0 < b)
    (hab : IsCoprime a b) (ha : a ≠ 0) (heq : -57600 * b * Fh p q ^ 2 = a * Gh p q ^ 6) :
    max p.natAbs q.natAbs ≤ 2 * 4000 ^ 6 * max a.natAbs b.natAbs := by
  have h1 := bound_p hpq ha heq
  have h2 := bound_q hq hpq hb hab heq
  have ha' := le_max_left a.natAbs b.natAbs
  have hb' := le_max_right a.natAbs b.natAbs
  refine max_le ?_ ?_
  · calc p.natAbs ≤ 3600 ^ 6 * a.natAbs := h1
      _ ≤ 3600 ^ 6 * max a.natAbs b.natAbs := Nat.mul_le_mul_left _ ha'
      _ ≤ 2 * 4000 ^ 6 * max a.natAbs b.natAbs := Nat.mul_le_mul_right _ (by norm_num)
  · calc q.natAbs ≤ 57600 * b.natAbs + 117649 * a.natAbs := h2
      _ ≤ 57600 * max a.natAbs b.natAbs + 117649 * max a.natAbs b.natAbs :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hb') (Nat.mul_le_mul_left _ ha')
      _ = 175249 * max a.natAbs b.natAbs := by ring
      _ ≤ 2 * 4000 ^ 6 * max a.natAbs b.natAbs := Nat.mul_le_mul_right _ (by norm_num)

theorem log_const_lt : Real.log (2 * 4000 ^ 6) < 74 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have : (2 * 4000 ^ 6 : ℝ) < 2.7 ^ 74 := by norm_num
  exact this.trans (by
    have h := Real.exp_one_gt_d9
    calc (2.7 : ℝ) ^ 74 < Real.exp 1 ^ 74 := by gcongr; linarith
      _ = Real.exp 74 := by rw [← Real.exp_nat_mul]; norm_num)

/-- Height form: `log max(|p|, q) ≤ log max(|a|, b) + log(2·4000⁶)`. -/
theorem log_height_bound {p q a b : ℤ} (hq : 0 < q) (hpq : IsCoprime p q) (hb : 0 < b)
    (hab : IsCoprime a b) (ha : a ≠ 0) (heq : -57600 * b * Fh p q ^ 2 = a * Gh p q ^ 6) :
    Real.log (max p.natAbs q.natAbs : ℕ) ≤ Real.log (max a.natAbs b.natAbs : ℕ) +
      Real.log (2 * 4000 ^ 6) := by
  have h := height_bound hq hpq hb hab ha heq
  have hpos : (0 : ℝ) < (max a.natAbs b.natAbs : ℕ) := by
    have : 0 < max a.natAbs b.natAbs := lt_max_of_lt_left (Int.natAbs_pos.2 ha)
    exact_mod_cast this
  have hqpos : (0 : ℝ) < (max p.natAbs q.natAbs : ℕ) := by
    have : 0 < max p.natAbs q.natAbs := lt_max_of_lt_right (by omega)
    exact_mod_cast this
  rw [← Real.log_mul hpos.ne' (by norm_num)]
  apply Real.log_le_log hqpos
  have : ((max p.natAbs q.natAbs : ℕ) : ℝ) ≤ ((2 * 4000 ^ 6 * max a.natAbs b.natAbs : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at this ⊢; linarith

end MCheck22P.L954
