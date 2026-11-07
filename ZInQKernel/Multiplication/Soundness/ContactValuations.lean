import ZInQKernel.Multiplication.Certificate.SlopePredicate
import ZInQKernel.Multiplication.Certificate.ConstantsProperties

/-!
# Valuations of the normalization at an odd contact prime

Blueprint: `multiplication/soundness/contact-valuations.md`.

Let `t ∉ 𝒞 ∪ {1}`, `η = ±1`, `q ∈ ℚ`, `R₀ = η F(t)/(t-1)⁸`, `a = 1 - R₀ q² ≠ 0` and
`R = ℓ² a² R₀`. At a prime `p` with `v_p(ℓ) = 0`, `ℓ ≠ 0` and `p > 61` (the article's `p ∉ S_b`
gives `p > 324` and `v_p(ℓ₀) = 0`), if `k = v_p(t - c)` is positive and odd for some `c ∈ 𝒞`, then
`v_p(t - c') = 0` for the other contact values and `v_p(t - 1) = 0`, so `v_p(R₀) = v_p(F(t)) = k`,
and `r = v_p(R)` is odd with `r ≤ k`.

`contact_valuations_of` takes the two properties of `p` used by the proof (`61 < p`,
`v_p(ℓ) = 0`) as hypotheses; `contact_valuations` is the article's statement, with `ℓ = ℓ₀` and
`p ∉ S_b`.
-/

namespace ZInQ.Mult



/-- Every contact value is an integer in `[-60, 0]`. -/
theorem exists_int_of_mem_contactSet {c : ℚ} (hc : c ∈ contactSet) :
    ∃ m : ℤ, c = m ∧ -60 ≤ m ∧ m ≤ 0 := by
  simp only [contactSet, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, by norm_num, le_rfl⟩
  · exact ⟨-15, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨-20, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨-24, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨-30, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨-60, by norm_num, by norm_num, by norm_num⟩

section

variable {p : ℕ} [hp : Fact p.Prime]

/-- If `v_p(x) > 0` and `v_p(y) = 0`, then `v_p(x + y) = 0`. -/
theorem padicValRat_add_eq_zero {x y : ℚ} (hx : 0 < padicValRat p x) (hy0 : y ≠ 0)
    (hy : padicValRat p y = 0) : padicValRat p (x + y) = 0 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hxy : x + y ≠ 0 := by
    intro h
    have : y = -x := by linarith
    rw [this, padicValRat.neg] at hy
    omega
  rw [padicValRat.add_eq_min hxy hx0 hy0 (by omega), hy]
  exact min_eq_right hx.le

theorem padicValRat_prod_eq_zero {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, f i ≠ 0 ∧ padicValRat p (f i) = 0) :
    (∏ i ∈ s, f i) ≠ 0 ∧ padicValRat p (∏ i ∈ s, f i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ⟨h1, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ⟨h3, h4⟩ := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha]
    exact ⟨mul_ne_zero h3 h1, by rw [padicValRat.mul h3 h1, h2, h4, add_zero]⟩

/-- **Valuations of the normalization at an odd contact prime.** -/
theorem contact_valuations_of (hp61 : 61 < p) {t η q ℓ c : ℚ} (ht : t ∉ contactSet) (ht1 : t ≠ 1)
    (hη : η = 1 ∨ η = -1) (hℓ0 : ℓ ≠ 0) (hℓ : padicValRat p ℓ = 0)
    (ha : slopeA (slopeR0 η t) q ≠ 0)
    (hc : c ∈ contactSet) (hk : 0 < padicValRat p (t - c)) (hodd : Odd (padicValRat p (t - c))) :
    (∀ c' ∈ contactSet, c' ≠ c → padicValRat p (t - c') = 0) ∧ padicValRat p (t - 1) = 0 ∧
      padicValRat p (slopeR0 η t) = padicValRat p (t - c) ∧
      padicValRat p (contactPoly t) = padicValRat p (t - c) ∧
      Odd (padicValRat p (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t))) ∧
      padicValRat p (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t)) ≤ padicValRat p (t - c) := by
  set k := padicValRat p (t - c) with hkdef
  obtain ⟨m, rfl, hm1, hm2⟩ := exists_int_of_mem_contactSet hc
  -- the other contact values
  have hother : ∀ c' ∈ contactSet, c' ≠ (m : ℚ) → padicValRat p (t - c') = 0 := by
    intro c' hc' hne
    obtain ⟨m', rfl, hm1', hm2'⟩ := exists_int_of_mem_contactSet hc'
    have hmm : m - m' ≠ 0 := by
      intro h; apply hne; rw [show m' = m by omega]
    have e : t - (m' : ℚ) = (t - m) + ((m - m' : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    exact padicValRat_add_eq_zero hk (by exact_mod_cast hmm)
      (padicValRat_intCast_eq_zero hmm (by omega))
  have hone : padicValRat p (t - 1) = 0 := by
    have hm1' : m - 1 ≠ 0 := by omega
    have e : t - 1 = (t - m) + ((m - 1 : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    exact padicValRat_add_eq_zero hk (by exact_mod_cast hm1')
      (padicValRat_intCast_eq_zero hm1' (by omega))
  have htc0 : t - (m : ℚ) ≠ 0 := by
    intro h; rw [hkdef, h, padicValRat.zero] at hk; exact lt_irrefl _ hk
  -- `v_p(F(t)) = k`
  have hF : padicValRat p (contactPoly t) = k := by
    rw [contactPoly_eq_prod, ← Finset.mul_prod_erase _ _ hc]
    obtain ⟨h0, hv⟩ := padicValRat_prod_eq_zero (p := p) ((contactSet).erase (m : ℚ))
      (fun c' => t - c') fun c' hc' => by
        obtain ⟨hne, hc'⟩ := Finset.mem_erase.mp hc'
        refine ⟨fun h => ht ?_, hother c' hc' hne⟩
        rw [sub_eq_zero] at h; rwa [h]
    rw [padicValRat.mul htc0 h0, hv, add_zero]
  have hF0 := contactPoly_ne_zero ht
  have ht10 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hη0 : η ≠ 0 := by rcases hη with rfl | rfl <;> norm_num
  have hηv : padicValRat p η = 0 := by
    rcases hη with rfl | rfl
    · exact padicValRat.one
    · rw [padicValRat.neg, padicValRat.one]
  set R₀ := slopeR0 η t with hR₀
  have hR₀0 : R₀ ≠ 0 := div_ne_zero (mul_ne_zero hη0 hF0) (pow_ne_zero _ ht10)
  have hR₀v : padicValRat p R₀ = k := by
    rw [hR₀, slopeR0, padicValRat.div (mul_ne_zero hη0 hF0) (pow_ne_zero _ ht10),
      padicValRat.mul hη0 hF0, padicValRat.pow, hηv, hF, hone]
    ring
  -- `v_p(a) ≤ 0` and `v_p(R) = 2 v_p(a) + k`
  set a := slopeA R₀ q with hadef
  have hav : padicValRat p a ≤ 0 := by
    by_cases hq : q = 0
    · rw [hadef, slopeA, hq]; simp
    have hRq0 : R₀ * q ^ 2 ≠ 0 := mul_ne_zero hR₀0 (pow_ne_zero _ hq)
    have hRqv : padicValRat p (R₀ * q ^ 2) = k + 2 * padicValRat p q := by
      rw [padicValRat.mul hR₀0 (pow_ne_zero _ hq), hR₀v, padicValRat.pow]; push_cast; ring
    have hne : padicValRat p (R₀ * q ^ 2) ≠ 0 := by
      rw [hRqv]; intro h
      obtain ⟨j, hj⟩ := hodd
      omega
    have e : a = 1 + -(R₀ * q ^ 2) := by rw [hadef, slopeA]; ring
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [e, padicValRat.add_eq_min (by rw [← e]; exact ha) one_ne_zero (neg_ne_zero.mpr hRq0)
        (by rw [padicValRat.neg, padicValRat.one]; omega), padicValRat.neg, padicValRat.one]
      exact min_le_left _ _
    · rw [e, add_comm, padicValRat_add_eq_zero (by rwa [padicValRat.neg]) one_ne_zero
        padicValRat.one]
  have hRv : padicValRat p (slopeR ℓ a R₀) = 2 * padicValRat p a + k := by
    rw [slopeR, padicValRat.mul (mul_ne_zero (pow_ne_zero _ hℓ0) (pow_ne_zero _ ha)) hR₀0,
      padicValRat.mul (pow_ne_zero _ hℓ0) (pow_ne_zero _ ha), padicValRat.pow, padicValRat.pow,
      hℓ, hR₀v]
    push_cast; ring
  refine ⟨hother, hone, hR₀v, hF, ?_, ?_⟩
  · rw [hRv]; exact Even.add_odd (even_two_mul _) hodd
  · rw [hRv]; omega

/-- A prime outside `S_b` exceeds `324`. -/
theorem lt_of_not_mem_S_b {q : ℕ} (hq : q.Prime) (h : q ∉ S_b) : 324 < q := by
  by_contra hle
  exact h (mem_S_b.2 (Or.inl (mem_S_ht.2 ⟨hq, by omega⟩)))

/-- `v_p(ℓ₀) = 0` for a prime `p ∉ S_b`. -/
theorem padicValRat_ell_of_not_mem (h : p ∉ S_b) : padicValRat p (Syntax.ell : ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat_ell_of_not_mem hp.out h, Nat.cast_zero]

theorem ell_cast_ne_zero : (Syntax.ell : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Syntax.ell_pos.ne'

/-- **Valuations of the normalization at an odd contact prime**, with `ℓ = ℓ₀` and `p ∉ S_b`. -/
theorem contact_valuations (hpS : p ∉ S_b) {t η q c : ℚ} (ht : t ∉ contactSet) (ht1 : t ≠ 1)
    (hη : η = 1 ∨ η = -1) (ha : slopeA (slopeR0 η t) q ≠ 0)
    (hc : c ∈ contactSet) (hk : 0 < padicValRat p (t - c)) (hodd : Odd (padicValRat p (t - c))) :
    (∀ c' ∈ contactSet, c' ≠ c → padicValRat p (t - c') = 0) ∧ padicValRat p (t - 1) = 0 ∧
      padicValRat p (slopeR0 η t) = padicValRat p (t - c) ∧
      padicValRat p (contactPoly t) = padicValRat p (t - c) ∧
      Odd (padicValRat p (slopeR (Syntax.ell : ℚ) (slopeA (slopeR0 η t) q) (slopeR0 η t))) ∧
      padicValRat p (slopeR (Syntax.ell : ℚ) (slopeA (slopeR0 η t) q) (slopeR0 η t)) ≤
        padicValRat p (t - c) :=
  contact_valuations_of (by have := lt_of_not_mem_S_b hp.out hpS; omega) ht ht1 hη
    ell_cast_ne_zero (padicValRat_ell_of_not_mem hpS) ha hc hk hodd

end

end ZInQ.Mult
