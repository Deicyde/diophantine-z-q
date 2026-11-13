import ZInQKernel.Multiplication.Completeness.PoleValuationsAux

/-!
# Slopes of an integer from the two-slope pattern

Hypothesis 22P₂ (`TwoSlopePattern`) gives, for every `A ∈ ℤ`, integers `u, v` such that the
twelve numbers `u - c v` and `u - (A + 10 - c) v` (`c ∈ 𝒞`) are, up to sign, good slope primes
outside `S_b`, and `v`, `u - v`, `u - (A + 9) v` have bounded valuations at `S_b`. Then
`A = u / v + (A + 10 - u / v) + (-10)`, and each of the three slopes satisfies `GoodSlope 0`:

* `u / v` and `A + 10 - u / v = ((A + 10) v - u) / v` by `goodSlope_of_primeValues`, since their
  contact numerators are `±` the twelve pattern primes;
* the constant `-10` by `goodSlope_neg_ten`: its contact values are `-10, 5, 10, 14, 20, 50`, so it
  has no odd contact prime outside `S_b`, and `F(-10)/(-11)^8 = -7·10⁶/11⁸`.

This proves the slope representation `SlopeRepresentation` from 22P₂
(`slopeRepresentation_of_twoSlopePattern`).
-/

namespace ZInQ.Mult

open scoped BigOperators

/-- An integer of absolute value below `q` that is not zero has `q`-adic valuation zero. -/
theorem padicValInt_eq_zero_of_natAbs_lt_twoSlope {q : ℕ} {x : ℤ} (hx : x ≠ 0)
    (h : x.natAbs < q) : padicValInt q x = 0 :=
  padicValInt.eq_zero_of_not_dvd fun hd =>
    absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hx) (Int.natCast_dvd.mp hd)) (by omega)

theorem padicValInt_neg_twoSlope (q : ℕ) (x : ℤ) : padicValInt q (-x) = padicValInt q x := by
  simp [padicValInt]

theorem one_le_Bp (p : ℕ) : 1 ≤ Bp p := by
  unfold Bp; split_ifs <;> norm_num

/-! ### Slopes whose contact numerators are primes -/

/-- If the six contact numerators `u - c v` (`c ∈ 𝒞`) are, up to sign, good slope primes outside
`S_b`, and `v` and `u - v` have valuation at most `B_q` at every `q ∈ S_b`, then `u / v` satisfies
`GoodSlope 0`. -/
theorem goodSlope_of_primeValues (u v : ℤ) (hv0 : v ≠ 0) (hu1 : u - v ≠ 0)
    (hprime : ∀ b ∈ contactInts, GoodSlopePrime (u - b * v).natAbs ∧ (u - b * v).natAbs ∉ S_b)
    (hold : ∀ q ∈ S_b, padicValInt q v ≤ Bp q ∧ padicValInt q (u - v) ≤ Bp q) :
    GoodSlope 0 ((u : ℚ) / v) := by
  classical
  have hvQ : (v : ℚ) ≠ 0 := by exact_mod_cast hv0
  have hp : ∀ b ∈ contactInts, (u - b * v).natAbs.Prime := fun b hb => (hprime b hb).1.1
  have hx0 : ∀ b ∈ contactInts, u - b * v ≠ 0 := fun b hb h => by
    have := hp b hb; rw [h] at this; exact Nat.not_prime_zero this
  -- valuations of a contact numerator
  have hle : ∀ (q : ℕ) [Fact q.Prime] (b : ℤ), b ∈ contactInts → padicValInt q (u - b * v) ≤ 1 :=
    fun q _ b hb => padicValNat_prime_le_one (hp b hb)
  have heq : ∀ (q : ℕ) [Fact q.Prime] (b : ℤ), b ∈ contactInts → padicValInt q (u - b * v) ≠ 0 →
      q = (u - b * v).natAbs := by
    intro q _ b hb hne
    by_contra hqp
    have : Fact (u - b * v).natAbs.Prime := ⟨hp b hb⟩
    exact hne (padicValNat_primes hqp)
  have hsub : ∀ b : ℤ, (u : ℚ) / v - b = ((u - b * v : ℤ) : ℚ) / v := by
    intro b; push_cast; field_simp
  have hvt : ∀ (q : ℕ) [Fact q.Prime] (b : ℤ), b ∈ contactInts →
      padicValRat q ((u : ℚ) / v - b) = padicValInt q (u - b * v) - padicValInt q v := by
    intro q _ b hb
    rw [hsub, padicValRat_div_int (hx0 b hb) hv0]
  -- a positive contact valuation at `q` forces `q` to be the prime of that numerator
  have hpos_ne : ∀ (q : ℕ) [Fact q.Prime] (b : ℤ), b ∈ contactInts →
      0 < padicValRat q ((u : ℚ) / v - b) → padicValInt q (u - b * v) ≠ 0 := by
    intro q _ b hb hpos h0
    rw [hvt q b hb, h0] at hpos
    push_cast at hpos
    linarith [(Int.natCast_nonneg (padicValInt q v) : (0 : ℤ) ≤ _)]
  have h1Q : (u : ℚ) / v - 1 = ((u - v : ℤ) : ℚ) / v := by push_cast; field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- condition 1: `t ∉ 𝒞`
    intro hmem
    obtain ⟨b, hb, hbt⟩ := mem_contactSet_iff.mp hmem
    apply hx0 b hb
    have h0 : ((u : ℚ) / v - b) = 0 := by rw [hbt]; ring
    rw [hsub] at h0
    exact_mod_cast (div_eq_zero_iff.mp h0).resolve_right hvQ
  · -- `t ≠ 1`
    intro h
    apply hu1
    have h0 : ((u : ℚ) / v - 1) = 0 := by rw [h]; ring
    rw [h1Q] at h0
    exact_mod_cast (div_eq_zero_iff.mp h0).resolve_right hvQ
  · -- condition 2
    intro q hq
    have hqp := prime_of_mem_S_b hq
    have : Fact q.Prime := ⟨hqp⟩
    obtain ⟨hBv, hBu⟩ := hold q hq
    have hBv' : (padicValInt q v : ℤ) ≤ Bp q := by exact_mod_cast hBv
    have hBu' : (padicValInt q (u - v) : ℤ) ≤ Bp q := by exact_mod_cast hBu
    have h0v := (Int.natCast_nonneg (padicValInt q v) : (0 : ℤ) ≤ _)
    have h0u := (Int.natCast_nonneg (padicValInt q (u - v)) : (0 : ℤ) ≤ _)
    -- the contact numerators are units at `q`
    have hzero : ∀ b ∈ contactInts, padicValInt q (u - b * v) = 0 := by
      intro b hb
      by_contra hne
      have := heq q b hb hne
      exact (hprime b hb).2 (this ▸ hq)
    constructor
    · rw [h1Q, padicValRat_div_int hu1 hv0, abs_le]
      constructor <;> linarith
    · -- `F(t)/(t-1)^8 = X v² / (u - v)^8` with `X = ∏_{c ∈ 𝒞} (u - c v)` a unit at `q`
      set X : ℤ := (u - 0 * v) * (u - (-15) * v) * (u - (-20) * v) * (u - (-24) * v) *
        (u - (-30) * v) * (u - (-60) * v) with hX
      have hmem : ∀ b ∈ ([0, -15, -20, -24, -30, -60] : List ℤ), b ∈ contactInts := fun b hb => hb
      have hX0 : X ≠ 0 := by
        simp only [hX]
        refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
          (hx0 0 (hmem 0 (by simp))) (hx0 (-15) (hmem (-15) (by simp))))
          (hx0 (-20) (hmem (-20) (by simp)))) (hx0 (-24) (hmem (-24) (by simp))))
          (hx0 (-30) (hmem (-30) (by simp)))) (hx0 (-60) (hmem (-60) (by simp)))
      have hXq : padicValInt q X = 0 := by
        have hq' : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hqp
        have hnd : ∀ b ∈ contactInts, ¬ (q : ℤ) ∣ u - b * v := fun b hb hd => by
          have h0 := hzero b hb
          rw [padicValInt.eq_zero_iff] at h0
          rcases h0 with h0 | h0 | h0
          · exact hqp.one_lt.ne' h0
          · exact hx0 b hb h0
          · exact h0 hd
        apply padicValInt.eq_zero_of_not_dvd
        simp only [hX, hq'.dvd_mul]
        rintro (((((h | h) | h) | h) | h) | h)
        · exact hnd 0 (hmem 0 (by simp)) h
        · exact hnd (-15) (hmem (-15) (by simp)) h
        · exact hnd (-20) (hmem (-20) (by simp)) h
        · exact hnd (-24) (hmem (-24) (by simp)) h
        · exact hnd (-30) (hmem (-30) (by simp)) h
        · exact hnd (-60) (hmem (-60) (by simp)) h
      have hu1Q : (u : ℚ) - v ≠ 0 := by
        have : ((u - v : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hu1
        push_cast at this; exact this
      have hF : contactPoly ((u : ℚ) / v) / ((u : ℚ) / v - 1) ^ 8 =
          (X : ℚ) * (v : ℚ) ^ 2 / ((u - v : ℤ) : ℚ) ^ 8 := by
        rw [show (u : ℚ) / v - 1 = ((u : ℚ) - v) / v by field_simp]
        simp only [hX]
        unfold contactPoly
        push_cast
        field_simp
        ring
      have hXQ : (X : ℚ) ≠ 0 := by exact_mod_cast hX0
      have hu1Q' : ((u - v : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hu1
      rw [hF, padicValRat.div (mul_ne_zero hXQ (pow_ne_zero _ hvQ)) (pow_ne_zero _ hu1Q'),
        padicValRat.mul hXQ (pow_ne_zero _ hvQ), padicValRat.pow, padicValRat.pow]
      simp only [padicValRat.of_int, hXq]
      rw [abs_le]
      push_cast
      constructor <;> linarith
  · -- condition 3
    intro q hqS hodd
    obtain ⟨hq, c, hcC, hpos, -⟩ := hodd
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨b, hb, rfl⟩ := mem_contactSet_iff.mp hcC
    have hqe := heq q b hb (hpos_ne q b hb hpos)
    refine ⟨by exact_mod_cast hq.pos, hqe ▸ (hprime b hb).1, ?_⟩
    intro c' hc' hpos'
    obtain ⟨b', hb', rfl⟩ := mem_contactSet_iff.mp hc'
    rw [hvt q b' hb'] at hpos' ⊢
    have := hle q b' hb'
    omega
  · -- condition 4
    refine ⟨((contactInts.map fun b => (u - b * v).natAbs).toFinset).filter
      (fun q => q ∉ S_b ∧ IsOddContactPrime ((u : ℚ) / v) q), ?_, ?_⟩
    · refine (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans ?_)
      simp [contactInts]
    · intro q
      rw [Finset.mem_filter, List.mem_toFinset]
      constructor
      · exact fun h => h.2
      · rintro ⟨hqS, hodd⟩
        refine ⟨?_, hqS, hodd⟩
        obtain ⟨hq, c, hcC, hpos, -⟩ := hodd
        have : Fact q.Prime := ⟨hq⟩
        obtain ⟨b, hb, rfl⟩ := mem_contactSet_iff.mp hcC
        exact List.mem_map.mpr ⟨b, hb, (heq q b hb (hpos_ne q b hb hpos)).symm⟩

/-! ### The constant slope `-10` -/

/-- `-10` has no odd contact prime outside `S_b`: its contact values `-10, 5, 10, 14, 20, 50` are
integers of absolute value below `324`. -/
theorem not_isOddContactPrime_neg_ten {q : ℕ} (hqS : q ∉ S_b) :
    ¬ IsOddContactPrime (-10) q := by
  rintro ⟨hq, c, hcC, hpos, -⟩
  have : Fact q.Prime := ⟨hq⟩
  have hq324 := le_of_not_mem_S_b hq hqS
  obtain ⟨b, hb, rfl⟩ := mem_contactSet_iff.mp hcC
  have hval : ∀ b ∈ contactInts, (-10 - b : ℤ) ≠ 0 ∧ (-10 - b : ℤ).natAbs ≤ 50 := by decide
  rw [show (-10 : ℚ) - b = ((-10 - b : ℤ) : ℚ) by push_cast; ring, padicValRat.of_int,
    padicValInt_eq_zero_of_natAbs_lt_twoSlope (hval b hb).1 (by have := (hval b hb).2; omega)]
    at hpos
  exact lt_irrefl _ hpos

/-- **The constant slope `-10` is good.** `F(-10) = -7·10⁶ = -2⁶·5⁶·7` and `-10 - 1 = -11`, so the
valuations in condition 2 are at most `13` at the primes `q ≤ 324` (where `8 B_q = 32`) and vanish
at the catalogue primes; there is no odd contact prime outside `S_b`. -/
theorem goodSlope_neg_ten : GoodSlope 0 (-10) := by
  refine ⟨by simp [contactSet], by norm_num, ?_, ?_, ⟨∅, by simp, fun q => ?_⟩⟩
  · intro q hq
    have hqp := prime_of_mem_S_b hq
    have : Fact q.Prime := ⟨hqp⟩
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    have h2 : padicValNat q 2 ≤ 1 := padicValNat_prime_le_one Nat.prime_two
    have h5 : padicValNat q 5 ≤ 1 := padicValNat_prime_le_one (by norm_num)
    have h7 : padicValNat q 7 ≤ 1 := padicValNat_prime_le_one (by norm_num)
    have h11 : padicValNat q 11 ≤ 1 := padicValNat_prime_le_one (by norm_num)
    -- at a catalogue prime all four valuations vanish
    have hcat : q ∉ S_ht → padicValNat q 2 = 0 ∧ padicValNat q 5 = 0 ∧ padicValNat q 7 = 0 ∧
        padicValNat q 11 = 0 := by
      intro hht
      have hc : q ∈ catalogueSet := mem_catalogue.mp ((mem_S_b.mp hq).resolve_left hht)
      have h324 := (catalogueSet_prime hc).2
      refine ⟨padicValNat_primes (by omega), padicValNat_primes (by omega),
        padicValNat_primes (by omega), padicValNat_primes (by omega)⟩
    have hBp : q ∉ S_ht → Bp q = 1 := Bp_of_not_mem_S_ht
    have hBp' : q ∈ S_ht → Bp q = 4 := Bp_of_mem_S_ht
    have hB1 := one_le_Bp q
    have hv11 : padicValRat q ((-10 : ℚ) - 1) = padicValNat q 11 := by
      rw [show (-10 : ℚ) - 1 = -((11 : ℕ) : ℚ) by norm_num, padicValRat.neg, padicValRat.of_nat]
    have hF : contactPoly (-10) / ((-10 : ℚ) - 1) ^ 8 =
        -(((2 ^ 6 * 5 ^ 6 * 7 : ℕ) : ℚ) / ((11 : ℕ) : ℚ) ^ 8) := by
      norm_num [contactPoly]
    have hvF : padicValRat q (contactPoly (-10) / ((-10 : ℚ) - 1) ^ 8) =
        6 * padicValNat q 2 + 6 * padicValNat q 5 + padicValNat q 7 - 8 * padicValNat q 11 := by
      rw [hF, padicValRat.neg, padicValRat.div (by norm_num) (by norm_num),
        padicValRat.pow, padicValRat.of_nat, padicValRat.of_nat,
        padicValNat.mul (by norm_num) (by norm_num), padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.pow, padicValNat.pow]
      push_cast; ring
    rw [hv11, hvF, abs_le, abs_le]
    by_cases hht : q ∈ S_ht
    · rw [hBp' hht]; omega
    · obtain ⟨e2, e5, e7, e11⟩ := hcat hht
      rw [hBp hht, e2, e5, e7, e11]; omega
  · intro q hqS hodd
    exact absurd hodd (not_isOddContactPrime_neg_ten hqS)
  · simp only [Finset.notMem_empty, false_iff, not_and]
    exact fun hqS => not_isOddContactPrime_neg_ten hqS

/-! ### The slope representation from 22P₂ -/

/-- `16 w` is never prime. -/
theorem not_prime_natAbs_sixteen_mul (w : ℤ) : ¬ (16 * w).natAbs.Prime := by
  rw [Int.natAbs_mul]
  intro h
  rcases Nat.prime_mul_iff.mp h with ⟨h16, -⟩ | ⟨-, h1⟩
  · norm_num at h16
  · norm_num at h1

/-- **Slopes of an integer from the two-slope pattern.** Under hypothesis 22P₂ every integer `A`
is `u / v + (A + 10 - u / v) + (-10)`, a sum of three slopes satisfying `GoodSlope 0`. -/
theorem slopeRepresentation_of_twoSlopePattern (h : TwoSlopePattern) : SlopeRepresentation := by
  intro A
  obtain ⟨u, v, hv0, hprime, hold⟩ := h A
  have hmem1 : ∀ b ∈ contactInts, u - b * v ∈ twoSlopeValues A u v := fun b hb =>
    List.mem_flatMap.mpr ⟨b, hb, by simp⟩
  have hmem2 : ∀ b ∈ contactInts, u - (A + 10 - b) * v ∈ twoSlopeValues A u v := fun b hb =>
    List.mem_flatMap.mpr ⟨b, hb, by simp⟩
  have hS : ∀ x ∈ twoSlopeValues A u v, GoodSlopePrime x.natAbs ∧ x.natAbs ∉ S_b := by
    intro x hx
    obtain ⟨hgood, h324, hcat⟩ := hprime x hx
    refine ⟨hgood, fun hS => ?_⟩
    rcases mem_S_b.mp hS with h | h
    · have := (mem_S_ht.mp h).2; omega
    · exact hcat (mem_catalogue.mp h)
  have hB : ∀ x ∈ [v, u - v, u - (A + 9) * v], ∀ q ∈ S_b, padicValInt q x ≤ Bp q := by
    intro x hx q hq
    have hqp := prime_of_mem_S_b hq
    by_cases hht : q ∈ S_ht
    · rw [Bp_of_mem_S_ht hht]
      exact (hold x hx q hqp).1 (mem_S_ht.mp hht).2
    · rw [Bp_of_not_mem_S_ht hht]
      exact (hold x hx q hqp).2 (mem_catalogue.mp ((mem_S_b.mp hq).resolve_left hht))
  -- the first slope `u / v`
  have hu1 : u - v ≠ 0 := by
    intro h0
    have := (hS _ (hmem1 (-15) (by simp [contactInts]))).1.1
    rw [show u - (-15) * v = 16 * v by linear_combination h0] at this
    exact not_prime_natAbs_sixteen_mul v this
  have hgood1 : GoodSlope 0 ((u : ℚ) / v) :=
    goodSlope_of_primeValues u v hv0 hu1 (fun b hb => hS _ (hmem1 b hb))
      (fun q hq => ⟨hB v (by simp) q hq, hB (u - v) (by simp) q hq⟩)
  -- the second slope `A + 10 - u / v = ((A + 10) v - u) / v`
  set u₂ : ℤ := (A + 10) * v - u with hu₂
  have hneg : ∀ b : ℤ, u₂ - b * v = -(u - (A + 10 - b) * v) := fun b => by rw [hu₂]; ring
  have hu₂1 : u₂ - v ≠ 0 := by
    intro h0
    have := (hS _ (hmem2 (-15) (by simp [contactInts]))).1.1
    rw [show u - (A + 10 - (-15)) * v = 16 * (-v) by linear_combination -h0] at this
    exact not_prime_natAbs_sixteen_mul (-v) this
  have hgood2 : GoodSlope 0 ((u₂ : ℚ) / v) := by
    refine goodSlope_of_primeValues u₂ v hv0 hu₂1 (fun b hb => ?_) (fun q hq => ?_)
    · rw [hneg b, Int.natAbs_neg]; exact hS _ (hmem2 b hb)
    · refine ⟨hB v (by simp) q hq, ?_⟩
      rw [show u₂ - v = -(u - (A + 9) * v) by rw [hu₂]; ring, padicValInt_neg_twoSlope]
      exact hB _ (by simp) q hq
  refine ⟨![(u : ℚ) / v, (u₂ : ℚ) / v, -10], ?_, fun j => ?_⟩
  · have hvQ : (v : ℚ) ≠ 0 := by exact_mod_cast hv0
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hu₂]
    push_cast
    field_simp
    ring
  · fin_cases j
    · exact hgood1
    · exact hgood2
    · exact goodSlope_neg_ten

end ZInQ.Mult
