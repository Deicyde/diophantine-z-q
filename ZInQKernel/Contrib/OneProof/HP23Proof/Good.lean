import ZInQKernel.Contrib.OneProof.HfxProof.TwoAdic

/-!
# hp23-proof: the subgroup `2^ℤ (1 + 4ℤ₂)` of `ℚ₂^×`

Task hp23-proof (report `docs/research/hp23-proof.md`). `Good x` says `x ∈ 2^ℤ (1 + 4ℤ₂)`, the kernel of
the character `χ₀` of `ℚ(i)` on `ℚ₂^×` (local class field theory is not used: only that this set is a
subgroup containing the squares and `2`, and not containing an integer `≡ 3 (mod 4)`). A positive rational
whose valuations at the odd primes are even lies in it (`good_rat`), and so does the reduced norm of an
element of `ℚ_p^×`-scaled `ℤ_p`-norm-one quaternions at an odd place whose square is a rational
times a local unit (`even_padicValRat_of_eq`).
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HP23Proof

open ZInQ.Contrib.T21Proof ZInQ.Contrib.HfxProof

/-- `x ∈ 2^ℤ (1 + 4ℤ_p)`; used at `p = 2`. -/
def Good {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) : Prop :=
  x ≠ 0 ∧ ∃ m : ℤ, ‖x * (2 : ℚ_[p]) ^ m - 1‖ ≤ 1 / 4

section General

variable {p : ℕ} [Fact p.Prime]

theorem norm_one_add_of_le {a : ℚ_[p]} (ha : ‖a‖ ≤ 1 / 4) : ‖1 + a‖ = 1 := by
  have h1 : ‖a‖ < ‖(1 : ℚ_[p])‖ := by rw [norm_one]; linarith
  rw [add_comm, Padic.add_eq_max_of_ne (ne_of_lt h1), max_eq_right (le_of_lt h1), norm_one]

theorem Good.ne_zero {x : ℚ_[p]} (hx : Good x) : x ≠ 0 := hx.1

theorem Good.mul {x y : ℚ_[p]} (hx : Good x) (hy : Good y) : Good (x * y) := by
  obtain ⟨hx0, m, hm⟩ := hx
  obtain ⟨hy0, m', hm'⟩ := hy
  refine ⟨mul_ne_zero hx0 hy0, m + m', ?_⟩
  have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
  have e : x * y * (2 : ℚ_[p]) ^ (m + m') - 1 =
      (x * 2 ^ m - 1) + (y * 2 ^ m' - 1) + (x * 2 ^ m - 1) * (y * 2 ^ m' - 1) := by
    rw [zpow_add₀ h2]; ring
  rw [e]
  have hab : ‖(x * 2 ^ m - 1) * (y * 2 ^ m' - 1)‖ ≤ 1 / 4 := by
    rw [norm_mul]
    calc _ ≤ (1 / 4 : ℝ) * (1 / 4) := mul_le_mul hm hm' (norm_nonneg _) (by norm_num)
      _ ≤ 1 / 4 := by norm_num
  exact le_trans (Padic.nonarchimedean _ _)
    (max_le (le_trans (Padic.nonarchimedean _ _) (max_le hm hm')) hab)

theorem Good.inv {x : ℚ_[p]} (hx : Good x) : Good x⁻¹ := by
  obtain ⟨hx0, m, hm⟩ := hx
  refine ⟨inv_ne_zero hx0, -m, ?_⟩
  set a := x * 2 ^ m - 1 with ha
  have h1 : ‖1 + a‖ = 1 := norm_one_add_of_le hm
  have h10 : (1 + a) ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  have hxa : x * 2 ^ m = 1 + a := by rw [ha]; ring
  have e : x⁻¹ * (2 : ℚ_[p]) ^ (-m) - 1 = -a / (1 + a) := by
    rw [zpow_neg, ← mul_inv, hxa]; field_simp; ring
  rw [e, norm_div, norm_neg, h1, div_one]; exact hm

theorem Good.of_norm {x : ℚ_[p]} (h : ‖x - 1‖ ≤ 1 / 4) : Good x := by
  refine ⟨?_, 0, by simpa using h⟩
  rintro rfl; rw [zero_sub, norm_neg, norm_one] at h; norm_num at h

theorem Good.one : Good (1 : ℚ_[p]) := Good.of_norm (by simp)

theorem Good.two_zpow (k : ℤ) : Good ((2 : ℚ_[p]) ^ k) := by
  refine ⟨zpow_ne_zero _ two_ne_zero, -k, ?_⟩
  rw [← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, sub_self, norm_zero]; norm_num

theorem Good.two : Good (2 : ℚ_[p]) := by simpa using Good.two_zpow (p := p) 1

theorem Good.div {x y : ℚ_[p]} (hx : Good x) (hy : Good y) : Good (x / y) := by
  rw [div_eq_mul_inv]; exact hx.mul hy.inv

theorem Good.of_mul_left {x y : ℚ_[p]} (hxy : Good (x * y)) (hx : Good x) : Good y := by
  have := hx.inv.mul hxy
  rwa [← mul_assoc, inv_mul_cancel₀ hx.ne_zero, one_mul] at this

theorem Good.of_mul_right {x y : ℚ_[p]} (hxy : Good (x * y)) (hy : Good y) : Good x := by
  rw [mul_comm] at hxy; exact hxy.of_mul_left hy

/-- At an odd place: if `a² = q c² e` with `e` a unit, the valuation of `q` is even. -/
theorem even_padicValRat_of_eq {q : ℚ} (hq : q ≠ 0) {a c e : ℚ_[p]} (ha : a ≠ 0) (hc : c ≠ 0)
    (he : ‖e‖ = 1) (h : a ^ 2 = (q : ℚ_[p]) * (c ^ 2 * e)) : Even (padicValRat p q) := by
  have he0 : e ≠ 0 := by intro h0; rw [h0, norm_zero] at he; exact zero_ne_one he
  have hq' : (q : ℚ_[p]) ≠ 0 := by exact_mod_cast hq
  have hve : e.valuation = 0 := by
    have h1 := Padic.norm_eq_zpow_neg_valuation he0
    rw [he] at h1
    have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast (Fact.out : p.Prime).one_lt.ne'
    have := (zpow_eq_one_iff_right₀ (by positivity) hp1).mp h1.symm
    omega
  have hv := congrArg Padic.valuation h
  rw [Padic.valuation_pow, Padic.valuation_mul hq' (mul_ne_zero (pow_ne_zero 2 hc) he0),
    Padic.valuation_mul (pow_ne_zero 2 hc) he0, Padic.valuation_pow, hve,
    Padic.valuation_ratCast] at hv
  exact ⟨a.valuation - c.valuation, by push_cast at hv; linarith⟩

end General

/-! ## At `p = 2` -/

theorem sq_sub_one_red4 : ∀ x : ZMod 4, x ≠ 0 → x ≠ 2 → x ^ 2 - 1 = 0 := by decide

theorem norm_two_two : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by
  have := Padic.norm_p (p := 2); exact_mod_cast this

theorem good_sq {c : ℚ_[2]} (hc : c ≠ 0) : Good (c ^ 2) := by
  set u : ℚ_[2] := c * (2 : ℚ_[2]) ^ (-c.valuation) with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_mul, norm_zpow, norm_two_two, Padic.norm_eq_zpow_neg_valuation hc, inv_zpow',
      neg_neg]
    push_cast
    rw [← zpow_add₀ (by norm_num)]
    simp
  set U : ℤ_[2] := ⟨u, le_of_eq hun⟩ with hU
  have hUn : ‖(U : ℚ_[2])‖ = 1 := hun
  obtain ⟨h0, h2⟩ := red4_ne_zero_two_of_unit hUn
  have hr : red4 (U ^ 2 - 1) = 0 := by
    rw [map_sub, map_pow, map_one]; exact sq_sub_one_red4 _ h0 h2
  have hn := red4_eq_zero_iff_norm hr
  refine ⟨pow_ne_zero 2 hc, 2 * (-c.valuation), ?_⟩
  have e : c ^ 2 * (2 : ℚ_[2]) ^ (2 * (-c.valuation)) - 1 = ((U ^ 2 - 1 : ℤ_[2]) : ℚ_[2]) := by
    rw [PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_one]
    show _ = u ^ 2 - 1
    have h2 : (2 : ℚ_[2]) ^ (2 * -c.valuation) = ((2 : ℚ_[2]) ^ (-c.valuation)) ^ 2 := by
      rw [← zpow_natCast, ← zpow_mul]; ring_nf
    rw [hu, h2, mul_pow]
  rw [e]; exact hn

theorem not_good_int {m : ℤ} (hm : m % 4 = 3) : ¬ Good ((m : ℚ_[2])) := by
  rintro ⟨-, j, hj⟩
  have hodd : Odd m := by rw [Int.odd_iff]; omega
  have hmn : ‖(m : ℚ_[2])‖ = 1 := norm_odd_int hodd
  have h1 : ‖(m : ℚ_[2]) * 2 ^ j‖ = 1 := by
    have := norm_one_add_of_le hj
    rwa [add_sub_cancel] at this
  have hj0 : j = 0 := by
    rw [norm_mul, hmn, one_mul, norm_zpow, norm_two_two] at h1
    exact (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp h1
  subst hj0
  rw [zpow_zero, mul_one] at hj
  have h4 : ‖((m - 1 : ℤ) : ℚ_[2])‖ ≤ ((2 : ℕ) : ℝ) ^ (-((2 : ℕ) : ℤ)) := by
    push_cast; norm_num; exact hj
  have hd := (Padic.norm_int_le_pow_iff_dvd (m - 1) 2).mp h4
  push_cast at hd
  omega

theorem good_nat : ∀ N : ℕ, 0 < N → (∀ r : ℕ, r.Prime → r ≠ 2 → Even (padicValNat r N)) →
    Good ((N : ℚ_[2])) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN hev
  by_cases h1 : N = 1
  · subst h1; simpa using (Good.one : Good (1 : ℚ_[2]))
  have hq := Nat.minFac_prime h1
  by_cases hq2 : N.minFac = 2
  · obtain ⟨M, hM⟩ := Nat.minFac_dvd N
    rw [hq2] at hM
    have hM0 : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · subst h; omega
      · exact h
    have hMN : M < N := by omega
    have hevM : ∀ r, r.Prime → r ≠ 2 → Even (padicValNat r M) := by
      intro r hr hr2
      have := Fact.mk hr
      have := hev r hr hr2
      rwa [hM, padicValNat.mul two_ne_zero hM0.ne', padicValNat_primes hr2, zero_add] at this
    rw [hM]; push_cast
    exact Good.two.mul (ih M hMN hM0 hevM)
  · have := Fact.mk hq
    have hv1 : 1 ≤ padicValNat N.minFac N := one_le_padicValNat_of_dvd hN.ne' (Nat.minFac_dvd N)
    have hv2 : 2 ≤ padicValNat N.minFac N := by
      obtain ⟨k, hk⟩ := hev _ hq hq2; omega
    have hd : N.minFac ^ 2 ∣ N := (pow_dvd_pow _ hv2).trans pow_padicValNat_dvd
    obtain ⟨M, hM⟩ := hd
    have hq1 : 2 ≤ N.minFac := hq.two_le
    have hq4 : 4 ≤ N.minFac ^ 2 := by nlinarith
    have hM0 : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · subst h; omega
      · exact h
    have hMN : M < N := by rw [hM]; nlinarith
    have hevM : ∀ r, r.Prime → r ≠ 2 → Even (padicValNat r M) := by
      intro r hr hr2
      have := Fact.mk hr
      have := hev r hr hr2
      rw [hM, padicValNat.mul (pow_ne_zero 2 hq.ne_zero) hM0.ne', padicValNat.pow _ 2] at this
      exact (Nat.even_add.mp this).mp (even_two_mul _)
    rw [hM]; push_cast
    exact (good_sq (by exact_mod_cast hq.ne_zero)).mul (ih M hMN hM0 hevM)

/-- A positive rational with even valuations at the odd primes lies in `2^ℤ (1 + 4ℤ₂)`. -/
theorem good_rat {q : ℚ} (hq : 0 < q) (hev : ∀ r : ℕ, r.Prime → r ≠ 2 → Even (padicValRat r q)) :
    Good ((q : ℚ_[2])) := by
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have hnumc : (q.num : ℚ_[2]) = ((q.num.natAbs : ℕ) : ℚ_[2]) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hnum.le]
  have e : (q : ℚ_[2]) = ((q.num.natAbs : ℕ) : ℚ_[2]) / ((q.den : ℕ) : ℚ_[2]) := by
    conv_lhs => rw [← Rat.num_div_den q]
    push_cast; rw [hnumc]
  have hcop := q.reduced
  have hboth : ∀ r : ℕ, r.Prime → r ≠ 2 →
      Even (padicValNat r q.num.natAbs) ∧ Even (padicValNat r q.den) := by
    intro r hr hr2
    have := Fact.mk hr
    have h := hev r hr hr2
    have hdef : padicValRat r q = (padicValNat r q.num.natAbs : ℤ) - padicValNat r q.den := rfl
    rw [hdef, Int.even_sub] at h
    by_cases hd : r ∣ q.den
    · have hn : ¬ r ∣ q.num.natAbs := fun hn =>
        hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hn hcop) hd)
      rw [padicValNat.eq_zero_of_not_dvd hn] at h ⊢
      exact ⟨⟨0, rfl⟩, by exact_mod_cast h.mp (by simp)⟩
    · rw [padicValNat.eq_zero_of_not_dvd hd] at h ⊢
      exact ⟨by exact_mod_cast h.mpr (by simp), ⟨0, rfl⟩⟩
  rw [e]
  exact (good_nat _ (Int.natAbs_pos.mpr hnum.ne') fun r hr hr2 => (hboth r hr hr2).1).div
    (good_nat _ q.den_pos fun r hr hr2 => (hboth r hr hr2).2)

end ZInQ.Contrib.HP23Proof
