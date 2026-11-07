import ZInQKernel.Multiplication.Completeness.PatternSlopes
import ZInQKernel.Multiplication.Completeness.PoleLocal
import ZInQKernel.Multiplication.Completeness.SquareDen
import ZInQKernel.Multiplication.Local.Valuations
import ZInQKernel.Multiplication.Local.PrimesAbove
import ZInQKernel.Multiplication.Certificate.SlopePredicate
import ZInQKernel.Multiplication.Soundness.CommonGroup
import ZInQKernel.Multiplication.Soundness.TestsToCongruence

/-!
# Auxiliary valuations for the pole input

Rational side: the valuation of `R₀ = η F(t)/(t - 1)⁸` is even at primes that are not odd
contact primes, and equal to one at an odd contact prime of a good slope outside `S_b`.

`K₀` side: the valuation of a rational at a prime `π ∣ p` of `ℤ[s]` is `e v_p` with `e ∈ {1, 2}`,
conjugation exchanges `π` and `σπ`, and `Tr y = y + σ y`.
-/

namespace ZInQ.Mult

open scoped BigOperators

/-! ### Rational valuations -/

theorem padicValRat_finset_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) {f : ι → ℚ}
    (hf : ∀ i ∈ s, f i ≠ 0) : padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem padicValRat_intCast_nonneg {p : ℕ} (n : ℤ) : 0 ≤ padicValRat p (n : ℚ) := by
  rw [padicValRat.of_int]; exact Int.natCast_nonneg _

/-- If `v_p(t) < 0` then `v_p(t - c) = v_p(t)` for an integer `c`. -/
theorem padicValRat_sub_int_of_neg {p : ℕ} [Fact p.Prime] {t : ℚ} (ht : padicValRat p t < 0)
    (c : ℤ) : padicValRat p (t - c) = padicValRat p t := by
  by_cases hc : c = 0
  · subst hc; simp
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hc0 : (-(c : ℚ)) ≠ 0 := by exact_mod_cast neg_ne_zero.mpr hc
  have hsum : t + -(c : ℚ) ≠ 0 := by
    intro h
    have : t = c := by linarith
    rw [this] at ht
    linarith [padicValRat_intCast_nonneg (p := p) c]
  rw [sub_eq_add_neg, padicValRat.add_eq_of_lt hsum ht0 hc0]
  rw [padicValRat.neg]
  exact lt_of_lt_of_le ht (padicValRat_intCast_nonneg c)

/-- The valuation of a difference of two distinct elements of `𝒞 ∪ {1}` at a prime `p > 61`
is `0`. -/
theorem padicValRat_contact_diff {p : ℕ} [Fact p.Prime] (hp : 61 < p) {c c' : ℚ}
    (hc : c ∈ insert 1 contactSet) (hc' : c' ∈ insert 1 contactSet) (hne : c ≠ c') :
    padicValRat p (c - c') = 0 := by
  have hmem : ∀ x ∈ insert (1 : ℚ) contactSet, ∃ b ∈ (1 :: contactInts), x = (b : ℚ) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨1, List.mem_cons_self, by simp⟩
    · obtain ⟨b, hb, rfl⟩ := mem_contactSet_iff.mp hx
      exact ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
  have hdec : ∀ b ∈ (1 :: contactInts), ∀ b' ∈ (1 :: contactInts), b ≠ b' → (b - b').natAbs ≤ 61 := by
    decide
  have key : ∃ n : ℤ, c - c' = n ∧ n ≠ 0 ∧ n.natAbs ≤ 61 := by
    obtain ⟨b, hb, rfl⟩ := hmem c hc
    obtain ⟨b', hb', rfl⟩ := hmem c' hc'
    have hbb : b ≠ b' := fun h => hne (by rw [h])
    exact ⟨b - b', by push_cast; ring, sub_ne_zero.mpr hbb, hdec b hb b' hb' hbb⟩
  obtain ⟨n, hn, hn0, hnle⟩ := key
  rw [hn, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd]
  · rfl
  · intro hdvd
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simp only [Int.natAbs_natCast] at this
    have := Nat.le_of_dvd (Int.natAbs_pos.mpr hn0) this
    omega

/-- `v_p(F(t)/(t-1)⁸) = Σ_c v_p(t - c) - 8 v_p(t - 1)`. -/
theorem padicValRat_contactQuot {p : ℕ} [Fact p.Prime] {t : ℚ} (ht : t ∉ contactSet)
    (ht1 : t ≠ 1) :
    padicValRat p (contactPoly t / (t - 1) ^ 8) =
      ∑ c ∈ contactSet, padicValRat p (t - c) - 8 * padicValRat p (t - 1) := by
  have hne : ∀ c ∈ contactSet, t - c ≠ 0 := fun c hc h => ht (by rwa [sub_eq_zero.mp h])
  rw [padicValRat.div (contactPoly_ne_zero ht) (pow_ne_zero _ (sub_ne_zero.mpr ht1)),
    padicValRat.pow, contactPoly_eq_prod, padicValRat_finset_prod _ hne]
  push_cast; ring

/-- At a prime that is not an odd contact prime of `t`, `v_p(F(t)/(t-1)⁸)` is even. -/
theorem even_padicValRat_contactQuot {p : ℕ} (hp : p.Prime) {t : ℚ} (ht : t ∉ contactSet)
    (ht1 : t ≠ 1) (hodd : ¬ IsOddContactPrime t p) :
    Even (padicValRat p (contactPoly t / (t - 1) ^ 8)) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValRat_contactQuot ht ht1]
  have hsum : Even (∑ c ∈ contactSet, padicValRat p (t - c)) := by
    by_cases hneg : padicValRat p t < 0
    · have : ∀ c ∈ contactSet, padicValRat p (t - c) = padicValRat p t := by
        intro c hc
        obtain ⟨b, -, rfl⟩ := mem_contactSet_iff.mp hc
        exact padicValRat_sub_int_of_neg hneg b
      rw [Finset.sum_congr rfl this, Finset.sum_const]
      have hcard : contactSet.card = 6 := by decide
      rw [hcard]
      exact ⟨3 * padicValRat p t, by simp only [nsmul_eq_mul]; push_cast; ring⟩
    · push Not at hneg
      refine Finset.even_sum _ fun c hc => ?_
      have hnn : 0 ≤ padicValRat p (t - c) := by
        obtain ⟨b, -, rfl⟩ := mem_contactSet_iff.mp hc
        by_cases h0 : t - b = 0
        · rw [h0]; simp
        have := padicValRat.min_le_padicValRat_add (p := p) (q := t) (r := -(b : ℚ))
          (by rwa [← sub_eq_add_neg])
        rw [padicValRat.neg, ← sub_eq_add_neg] at this
        have := padicValRat_intCast_nonneg (p := p) b
        omega
      rcases hnn.lt_or_eq with hpos | h0
      · by_contra hne
        exact hodd ⟨hp, c, hc, hpos, Int.not_even_iff_odd.mp hne⟩
      · rw [← h0]; exact ⟨0, rfl⟩
  have : 8 * padicValRat p (t - 1) = 2 * (4 * padicValRat p (t - 1)) := by ring
  rw [this]
  exact hsum.sub (even_two_mul _)

theorem le_of_not_mem_S_b {p : ℕ} (hp : p.Prime) (hpS : p ∉ S_b) : 324 < p := by
  by_contra h
  exact hpS (mem_S_b.mpr (Or.inl (mem_S_ht.mpr ⟨hp, by omega⟩)))

/-- At an odd contact prime `p ∉ S_b` of a good slope, `v_p(F(t)/(t-1)⁸) = 1` and
`v_p(t - 1) = 0`. -/
theorem padicValRat_contactQuot_eq_one {B₀ : ℝ} {t : ℚ} (ht : GoodSlope B₀ t) {p : ℕ}
    (hpS : p ∉ S_b) (hodd : IsOddContactPrime t p) :
    padicValRat p (contactPoly t / (t - 1) ^ 8) = 1 ∧ padicValRat p (t - 1) = 0 := by
  have hp := hodd.1
  have : Fact p.Prime := ⟨hp⟩
  have hp61 : 61 < p := by have := le_of_not_mem_S_b hp hpS; omega
  obtain ⟨-, -, hone⟩ := ht.contact p hpS hodd
  obtain ⟨-, c₀, hc₀, hpos, -⟩ := hodd
  have h1 := hone c₀ hc₀ hpos
  -- every other value `t - c` has valuation `0`
  have hother : ∀ c ∈ insert 1 contactSet, c ≠ c₀ → padicValRat p (t - c) = 0 := by
    intro c hc hne
    have hd := padicValRat_contact_diff hp61 (Finset.mem_insert_of_mem hc₀) hc hne.symm
    have hd0 : c₀ - c ≠ 0 := sub_ne_zero.mpr hne.symm
    have ht0 : t - c₀ ≠ 0 := by intro h; rw [h] at h1; simp at h1
    have hsum : (c₀ - c) + (t - c₀) ≠ 0 := by
      intro h
      have : t = c := by linarith
      have := ht.not_mem_contactSet
      rcases Finset.mem_insert.mp hc with rfl | hc'
      · exact ht.ne_one this
      · exact ht.not_mem_contactSet (by rw [‹t = c›]; exact hc')
    have e : t - c = (c₀ - c) + (t - c₀) := by ring
    rw [e, padicValRat.add_eq_of_lt hsum hd0 ht0 (by rw [hd, h1]; norm_num), hd]
  have ht1 : padicValRat p (t - 1) = 0 := by
    have : (1 : ℚ) ≠ c₀ := fun h => by
      rw [← h] at hc₀
      simp [contactSet] at hc₀
      norm_num at hc₀
    exact hother 1 (Finset.mem_insert_self _ _) this
  refine ⟨?_, ht1⟩
  rw [padicValRat_contactQuot ht.not_mem_contactSet ht.ne_one, ht1,
    Finset.sum_eq_single c₀ (fun c hc hne => hother c (Finset.mem_insert_of_mem hc) hne)
      (fun h => absurd hc₀ h), h1]
  norm_num

/-- The contact value of condition 3 is unique: at a prime `p ∉ S_b` at most one `t - c`
(`c ∈ 𝒞`) has positive valuation. -/
theorem contact_unique {t : ℚ} (ht : t ∉ contactSet) {p : ℕ} (hp : p.Prime) (hpS : p ∉ S_b)
    {c c' : ℚ} (hc : c ∈ contactSet) (hc' : c' ∈ contactSet) (h1 : 0 < padicValRat p (t - c))
    (h2 : 0 < padicValRat p (t - c')) : c = c' := by
  have : Fact p.Prime := ⟨hp⟩
  have hp61 : 61 < p := by have := le_of_not_mem_S_b hp hpS; omega
  by_contra hne
  have hd := padicValRat_contact_diff hp61 (Finset.mem_insert_of_mem hc)
    (Finset.mem_insert_of_mem hc') hne
  have hd0 : c - c' ≠ 0 := sub_ne_zero.mpr hne
  have ht0 : t - c ≠ 0 := fun h => ht (by rw [sub_eq_zero.mp h]; exact hc)
  have hsum : (c - c') + (t - c) ≠ 0 := fun h => ht (by
    have : t = c' := by linarith
    rw [this]; exact hc')
  have e : t - c' = (c - c') + (t - c) := by ring
  rw [e, padicValRat.add_eq_of_lt hsum hd0 ht0 (by rw [hd]; exact h1), hd] at h2
  exact lt_irrefl 0 h2

/-- `v_p(1 - x) = 0` when `v_p(x) > 0` or `x = 0`. -/
theorem padicValRat_one_sub {p : ℕ} [Fact p.Prime] {x : ℚ} (hx : x = 0 ∨ 0 < padicValRat p x) :
    padicValRat p (1 - x) = 0 := by
  rcases hx with rfl | hx
  · simp
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  by_cases h : 1 - x = 0
  · rw [h]; simp
  rw [sub_eq_add_neg, padicValRat.add_eq_of_lt (by rwa [← sub_eq_add_neg]) one_ne_zero
    (neg_ne_zero.mpr hx0) (by rw [padicValRat.neg]; simpa using hx)]
  simp

theorem padicValRat_eta {p : ℕ} {η : ℚ} (hη : η = 1 ∨ η = -1) : padicValRat p η = 0 := by
  rcases hη with rfl | rfl
  · simp
  · rw [padicValRat.neg]; simp

/-! ### Valuations of `K₀` at a prime above `p` -/

theorem vP_ratCast_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π)
    (hπp : π ∣ (p : Zs)) {r : ℚ} (hr : r ≠ 0) :
    vP π hπ (r : K0) = ((padicValRat p r : ℤ) : WithTop ℤ) := by
  rw [vP_apply hπ (by exact_mod_cast hr), vp_ratCast hp2 hπ hπp]

theorem trace_cast_K0 (y : K0) :
    ((QuadraticAlgebra.trace y : ℚ) : K0) = y + star y := by
  rw [K0.trace_eq]; ext <;> simp [K0.star_eq']; ring

/-- At a prime `π ∣ p` the valuation of a nonzero rational is `e v_p` with `e ∈ {1, 2}`. -/
theorem exists_vP_ratCast {p : ℕ} (hp : p.Prime) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs)) :
    ∃ e : ℤ, 1 ≤ e ∧ ∀ r : ℚ, r ≠ 0 → vP π hπ (r : K0) = ((e * padicValRat p r : ℤ) : WithTop ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨2, by norm_num, fun r hr => ?_⟩
    have hdvd : π ∣ sqrt2Z := by
      have : π ∣ sqrt2Z ^ 2 := by rw [← two_eq_sqrt2Z_sq]; exact_mod_cast hπp
      exact hπ.dvd_of_dvd_pow this
    have hass := hπ.associated_of_dvd prime_sqrt2Z hdvd
    rw [vP_apply hπ (by exact_mod_cast hr), vp_eq_of_associated hass, vS_rat hr]
  · exact ⟨1, le_rfl, fun r hr => by rw [vP_ratCast_odd hp2 hπ hπp hr, one_mul]⟩

end ZInQ.Mult
