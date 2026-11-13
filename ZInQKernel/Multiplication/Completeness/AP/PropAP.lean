import ZInQKernel.Multiplication.Completeness.AP.Completeness
import ZInQKernel.Hypotheses.PrimeAP

/-!
# Proposition AP: the slope representation from hypothesis 22P_AP

Route AP of `docs/research/nt-22p.md`, §3.3. Given `A`, put `A′ = A + 10`,
`T = 𝒞 ∪ {1}`, `S_A⁺ = T ∪ (A′ - T)`, and take a progression `x + j v` (`j ≤ K_A`) of good slope
primes above `max S_b`, with `K_A = max S_A⁺ - min S_A⁺`. With `u = x + (max S_A⁺) v` the numbers
`u - c′ v` (`c′ ∈ S_A⁺`) are terms of the progression. The slopes `t₁ = u/v`,
`t₂ = A′ - u/v = (A′ v - u)/v` and `t₃ = -10` sum to `A`; `t₁ > max S_A⁺ ≥ 1` and
`t₂ < -60` give `F(t₁), F(t₂) > 0`; and field 2′ holds at every old prime, with field 2 when
`v_ℓ(v) ≤ B_ℓ` and with the hypotheses of Lemma P otherwise (`goodSlopeAP_of_progression`).
Fields 3 and 4 are the argument of `goodSlope_of_primeValues`.

Here `max S_A⁺ = max(1, A′ + 60)` and `min S_A⁺ = min(-60, A′ - 1)`.
-/

namespace ZInQ.Mult

open scoped BigOperators

theorem contactPoly_pos_of_pos {t : ℚ} (ht : 0 < t) : 0 < contactPoly t := by
  unfold contactPoly
  have h1 : 0 < t + 15 := by linarith
  have h2 : 0 < t + 20 := by linarith
  have h3 : 0 < t + 24 := by linarith
  have h4 : 0 < t + 30 := by linarith
  have h5 : 0 < t + 60 := by linarith
  positivity

theorem contactPoly_pos_of_lt {t : ℚ} (ht : t < -60) : 0 < contactPoly t := by
  have e : contactPoly t =
      (-t) * (-(t + 15)) * (-(t + 20)) * (-(t + 24)) * (-(t + 30)) * (-(t + 60)) := by
    unfold contactPoly; ring
  rw [e]
  have h0 : 0 < -t := by linarith
  have h1 : 0 < -(t + 15) := by linarith
  have h2 : 0 < -(t + 20) := by linarith
  have h3 : 0 < -(t + 24) := by linarith
  have h4 : 0 < -(t + 30) := by linarith
  have h5 : 0 < -(t + 60) := by linarith
  positivity

/-- **A slope from a progression is good in the sense of field 2′.** If the seven numbers
`u - b v` (`b ∈ 𝒞 ∪ {1}`) are, up to sign, primes larger than every prime of `S_b`, the six with
`b ∈ 𝒞` are good slope primes, `v > 0` and `F(u/v) > 0`, then `u / v` satisfies
`GoodSlopeAP 0`. -/
theorem goodSlopeAP_of_progression (u v : ℤ) (hv : 0 < v)
    (hpr : ∀ b ∈ patternShifts, (u - b * v).natAbs.Prime ∧ ∀ q ∈ S_b, q < (u - b * v).natAbs)
    (hgood : ∀ b ∈ contactInts, GoodSlopePrime (u - b * v).natAbs)
    (hF : 0 < contactPoly ((u : ℚ) / v)) :
    GoodSlopeAP 0 ((u : ℚ) / v) := by
  classical
  have hv0 : v ≠ 0 := hv.ne'
  have hvQ : (v : ℚ) ≠ 0 := by exact_mod_cast hv0
  have hmem : ∀ b ∈ ([0, -15, -20, -24, -30, -60, 1] : List ℤ), b ∈ patternShifts :=
    fun b hb => hb
  have hprime : ∀ b ∈ contactInts, GoodSlopePrime (u - b * v).natAbs ∧
      (u - b * v).natAbs ∉ S_b := fun b hb =>
    ⟨hgood b hb, fun hS => by
      have := (hpr b (contactInts_sub_patternShifts hb)).2 _ hS; omega⟩
  have hp : ∀ b ∈ contactInts, (u - b * v).natAbs.Prime := fun b hb => (hprime b hb).1.1
  have hx0 : ∀ b ∈ contactInts, u - b * v ≠ 0 := fun b hb h => by
    have := hp b hb; rw [h] at this; exact Nat.not_prime_zero this
  have hu1 : u - v ≠ 0 := by
    intro h
    have := (hpr 1 (hmem 1 (by simp))).1
    rw [one_mul, h] at this; exact Nat.not_prime_zero this
  -- `u` and `v` are coprime
  have hcop : Nat.Coprime u.natAbs v.natAbs := by
    apply Nat.coprime_of_dvd
    intro k hk hku hkv
    have hku' : (k : ℤ) ∣ u := Int.natCast_dvd.mpr hku
    have hkv' : (k : ℤ) ∣ v := Int.natCast_dvd.mpr hkv
    have hk_eq : ∀ b ∈ contactInts, k = (u - b * v).natAbs := fun b hb =>
      (Nat.prime_dvd_prime_iff_eq hk (hp b hb)).mp
        (Int.natCast_dvd.mp (dvd_sub hku' (dvd_mul_of_dvd_right hkv' b)))
    have e0 := hk_eq 0 (by simp [contactInts])
    have e15 := hk_eq (-15) (by simp [contactInts])
    have e20 := hk_eq (-20) (by simp [contactInts])
    rw [e0] at e15 e20
    rcases Int.natAbs_eq_natAbs_iff.mp e15 with h | h <;>
      rcases Int.natAbs_eq_natAbs_iff.mp e20 with h' | h' <;> omega
  have hnum : ((u : ℚ) / v).num = u := Rat.num_div_eq_of_coprime hv hcop
  have hden : ((((u : ℚ) / v).den : ℕ) : ℤ) = v := Rat.den_div_eq_of_coprime hv hcop
  -- the facts of `goodSlope_of_primeValues`
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
  have hpos_ne : ∀ (q : ℕ) [Fact q.Prime] (b : ℤ), b ∈ contactInts →
      0 < padicValRat q ((u : ℚ) / v - b) → padicValInt q (u - b * v) ≠ 0 := by
    intro q _ b hb hpos h0
    rw [hvt q b hb, h0] at hpos
    push_cast at hpos
    linarith [(Int.natCast_nonneg (padicValInt q v) : (0 : ℤ) ≤ _)]
  have h1Q : (u : ℚ) / v - 1 = ((u - v : ℤ) : ℚ) / v := by push_cast; field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- condition 1: `t ∉ 𝒞`
    intro hmem'
    obtain ⟨b, hb, hbt⟩ := mem_contactSet_iff.mp hmem'
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
  · -- condition 2′
    intro ℓ hℓS
    have hℓp := prime_of_mem_S_b hℓS
    have : Fact ℓ.Prime := ⟨hℓp⟩
    have hnd : ∀ b ∈ patternShifts, ¬ (ℓ : ℤ) ∣ u - b * v := by
      intro b hb hd
      obtain ⟨hP, hlt⟩ := hpr b hb
      have := (Nat.prime_dvd_prime_iff_eq hℓp hP).mp (Int.natCast_dvd.mp hd)
      have := hlt ℓ hℓS; omega
    have hX := not_dvd_apContactNum hℓp (fun c hc => hnd c (contactInts_sub_patternShifts hc))
    have hX0 : apContactNum u v ≠ 0 := fun h => hX (by rw [h]; exact dvd_zero _)
    have hXQ : (apContactNum u v : ℚ) ≠ 0 := by exact_mod_cast hX0
    have hu1nd : ¬ (ℓ : ℤ) ∣ u - v := by
      have := hnd 1 (by simp [patternShifts]); simpa using this
    have hu1Q : ((u - v : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hu1
    obtain ⟨e, he⟩ : ∃ e : ℕ, padicValInt ℓ v = e := ⟨_, rfl⟩
    have hvt1 : padicValRat ℓ ((u : ℚ) / v - 1) = -e := by
      rw [h1Q, padicValRat_div_int hu1 hv0, padicValInt.eq_zero_of_not_dvd hu1nd, he]; simp
    have hvF : padicValRat ℓ (contactPoly ((u : ℚ) / v) / ((u : ℚ) / v - 1) ^ 8) = 2 * e := by
      rw [contactQuot_apContactNum hv0 hu1,
        padicValRat.div (mul_ne_zero hXQ (pow_ne_zero _ hvQ)) (pow_ne_zero _ hu1Q),
        padicValRat.mul hXQ (pow_ne_zero _ hvQ), padicValRat.pow, padicValRat.pow]
      simp only [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hX,
        padicValInt.eq_zero_of_not_dvd hu1nd, he]
      push_cast; ring
    by_cases heB : e ≤ Bp ℓ
    · left
      refine ⟨?_, ?_⟩
      · rw [hvt1, abs_neg, abs_of_nonneg (by positivity)]; exact_mod_cast heB
      · rw [hvF, abs_of_nonneg (by positivity)]
        have : (e : ℤ) ≤ Bp ℓ := by exact_mod_cast heB
        linarith
    · right
      refine ⟨hF, ?_⟩
      have hden' : padicValNat ℓ ((u : ℚ) / v).den = e := by
        have h := congrArg (padicValInt ℓ) hden
        rw [padicValInt.of_nat] at h
        rw [h, he]
      refine ⟨by rw [hden']; have := one_le_Bp ℓ; omega, fun h2 => ?_, fun c hc => ?_⟩
      · rw [hden']
        subst h2
        have : Bp 2 = 4 := Bp_of_mem_S_ht (mem_S_ht.mpr ⟨Nat.prime_two, by norm_num⟩)
        omega
      · rw [hnum, hden]; exact hnd c hc
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

theorem mem_patternShifts_bounds {b : ℤ} (hb : b ∈ patternShifts) : -60 ≤ b ∧ b ≤ 1 := by
  simp only [patternShifts, List.mem_cons, List.not_mem_nil, or_false] at hb
  omega

/-- **Proposition AP.** Hypothesis 22P_AP gives the slope representation under field 2′. -/
theorem slopeRepresentationAP_of_goodPrimeAP (hAP : GoodPrimeAP) : SlopeRepresentationAP := by
  intro A
  set A' : ℤ := A + 10 with hA'
  set mx : ℤ := max 1 (A' + 60) with hmx
  set mn : ℤ := min (-60) (A' - 1) with hmn
  obtain ⟨x, v, hx1, hv1, hprog⟩ := hAP (mx - mn).toNat
  set u : ℤ := x + mx * v with hu
  have hvpos : (0 : ℤ) < v := by exact_mod_cast hv1
  -- every `u - c′ v` with `mn ≤ c′ ≤ mx` is a term of the progression
  have hterm : ∀ c' : ℤ, mn ≤ c' → c' ≤ mx →
      GoodSlopePrime (u - c' * v).natAbs ∧ ∀ q ∈ S_b, q < (u - c' * v).natAbs := by
    intro c' h1 h2
    obtain ⟨hg, hb⟩ := hprog (mx - c').toNat (by omega)
    have e : u - c' * v = ((x + (mx - c').toNat * v : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg (by omega), hu]
      ring
    rw [e, Int.natAbs_natCast]
    exact ⟨hg, hb⟩
  have hmx1 : 1 ≤ mx := le_max_left _ _
  have hmx2 : A' + 60 ≤ mx := le_max_right _ _
  have hmn1 : mn ≤ -60 := min_le_left _ _
  have hmn2 : mn ≤ A' - 1 := min_le_right _ _
  -- the first slope `u / v`
  have hvQ : (v : ℚ) ≠ 0 := by positivity
  have ht1gt : (mx : ℚ) < (u : ℚ) / ((v : ℤ) : ℚ) := by
    rw [lt_div_iff₀ (by exact_mod_cast hvpos), hu]
    push_cast
    have : (0 : ℚ) < x := by exact_mod_cast hx1
    linarith
  have hgood1 : GoodSlopeAP 0 ((u : ℚ) / ((v : ℤ) : ℚ)) := by
    refine goodSlopeAP_of_progression u v hvpos (fun b hb => ?_) (fun b hb => ?_) ?_
    · have hbb := mem_patternShifts_bounds hb
      obtain ⟨hg, hlt⟩ := hterm b (by omega) (by omega)
      exact ⟨hg.1, hlt⟩
    · have hbb := mem_patternShifts_bounds (contactInts_sub_patternShifts hb)
      exact (hterm b (by omega) (by omega)).1
    · apply contactPoly_pos_of_pos
      have : (1 : ℚ) ≤ mx := by exact_mod_cast hmx1
      linarith
  -- the second slope `A′ - u / v = (A′ v - u) / v`
  set u₂ : ℤ := A' * v - u with hu₂
  have hneg : ∀ b : ℤ, u₂ - b * v = -(u - (A' - b) * v) := fun b => by rw [hu₂]; ring
  have hgood2 : GoodSlopeAP 0 ((u₂ : ℚ) / ((v : ℤ) : ℚ)) := by
    refine goodSlopeAP_of_progression u₂ v hvpos (fun b hb => ?_) (fun b hb => ?_) ?_
    · have hbb := mem_patternShifts_bounds hb
      obtain ⟨hg, hlt⟩ := hterm (A' - b) (by omega) (by omega)
      rw [hneg b, Int.natAbs_neg]
      exact ⟨hg.1, hlt⟩
    · have hbb := mem_patternShifts_bounds (contactInts_sub_patternShifts hb)
      rw [hneg b, Int.natAbs_neg]
      exact (hterm (A' - b) (by omega) (by omega)).1
    · apply contactPoly_pos_of_lt
      have e : (u₂ : ℚ) / ((v : ℤ) : ℚ) = A' - (u : ℚ) / ((v : ℤ) : ℚ) := by
        rw [hu₂]; push_cast; field_simp
      rw [e]
      have : ((A' + 60 : ℤ) : ℚ) ≤ mx := by exact_mod_cast hmx2
      push_cast at this
      linarith
  refine ⟨![(u : ℚ) / ((v : ℤ) : ℚ), (u₂ : ℚ) / ((v : ℤ) : ℚ), -10], ?_, fun j => ?_⟩
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hu₂, hA']
    push_cast
    field_simp
    ring
  · fin_cases j
    · exact hgood1
    · exact hgood2
    · exact goodSlope_neg_ten.goodSlopeAP

end ZInQ.Mult
