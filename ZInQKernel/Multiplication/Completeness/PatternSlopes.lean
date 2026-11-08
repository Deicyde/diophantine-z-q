import ZInQKernel.Multiplication.Completeness.PatternValues
import ZInQKernel.Multiplication.Certificate.ConstantsProperties

/-!
# Slopes of an integer from the prime pattern

Blueprint: `multiplication/completeness/pattern-slopes.md`.

Hypothesis 22P writes every integer `A` as `t₁ + t₂ + t₃` with `t_j = u_j / v`, where `v` and
all `u_j - b v` (`b ∈ 𝒞 ∪ {1}`) are pattern values `ε k p`. Each slope then satisfies the four
conditions `GoodSlope B₀ t`: it avoids `𝒞 ∪ {1}`, has bounded valuations at the old primes `S_b`,
its odd contact primes outside `S_b` are good slope primes (`GoodSlopePrime`) above `B₀` with
contact valuation one, and there are at most six of them.

`SlopeRepresentation` is what the rest of the completeness proof consumes: every integer is a sum
of three slopes satisfying `GoodSlope 0`. It follows from 22P
(`slopeRepresentation_of_fixedPrimePattern`) and from the two-slope pattern 22P₂ (`TwoSlope.lean`).
-/

namespace ZInQ.Mult

open scoped BigOperators

/-- Conditions 1-4 of the slopes from the prime pattern, for the bound `B₀`. Condition 4 is
stated with the explicit set `P` of odd contact primes outside `S_b`, of size at most six. -/
structure GoodSlope (B₀ : ℝ) (t : ℚ) : Prop where
  not_mem_contactSet : t ∉ contactSet
  ne_one : t ≠ 1
  old : ∀ p ∈ S_b, |padicValRat p (t - 1)| ≤ Bp p ∧
    |padicValRat p (contactPoly t / (t - 1) ^ 8)| ≤ 8 * Bp p
  contact : ∀ p : ℕ, p ∉ S_b → IsOddContactPrime t p →
    B₀ < p ∧ GoodSlopePrime p ∧
      ∀ c ∈ contactSet, 0 < padicValRat p (t - c) → padicValRat p (t - c) = 1
  few : ∃ P : Finset ℕ, P.card ≤ 6 ∧ ∀ p, p ∈ P ↔ p ∉ S_b ∧ IsOddContactPrime t p

/-- The "in particular" of condition 2: both valuations are at most `C_p = 14 B_p`. -/
theorem GoodSlope.old_le_Cp {B₀ : ℝ} {t : ℚ} (ht : GoodSlope B₀ t) {p : ℕ} (hp : p ∈ S_b) :
    |padicValRat p (t - 1)| ≤ Cp p ∧ |padicValRat p (contactPoly t / (t - 1) ^ 8)| ≤ Cp p := by
  obtain ⟨h1, h2⟩ := ht.old p hp
  unfold Cp; push_cast
  constructor <;> linarith [(Nat.cast_nonneg (Bp p) : (0 : ℤ) ≤ Bp p)]

/-! ### One pattern value -/

/-- The valuations of a pattern value `ε k p` with `p > 324`, `p` outside the catalogue. -/
theorem pattern_value_spec {ε : ℤ} {k p : ℕ} (hε : ε = 1 ∨ ε = -1)
    (hk : k ∈ catalogueMultipliers) (hp : p.Prime) (hp324 : 324 < p) (hpcat : p ∉ catalogueSet) :
    ε * k * p ≠ 0 ∧ (∀ q ∈ S_b, padicValInt q (ε * k * p) ≤ Bp q) ∧
      ∀ q : ℕ, q.Prime → q ∉ S_b → padicValInt q (ε * k * p) ≠ 0 →
        q = p ∧ padicValInt q (ε * k * p) = 1 := by
  have hk0 := pos_of_mem_catalogueMultipliers hk
  refine ⟨?_, ?_, ?_⟩
  · have : (ε : ℤ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    exact mul_ne_zero (mul_ne_zero this (by exact_mod_cast hk0.ne')) (by exact_mod_cast hp.ne_zero)
  · intro q hq
    have hqp := prime_of_mem_S_b hq
    have : Fact q.Prime := ⟨hqp⟩
    have : Fact p.Prime := ⟨hp⟩
    rw [padicValInt_pattern_value hε hk0 hp]
    rcases mem_S_b.mp hq with h | h
    · have hq324 := (mem_S_ht.mp h).2
      rw [padicValNat_primes (by omega : q ≠ p), Bp_of_mem_S_ht h]
      have := padicValNat_multiplier_le_small hk hqp hq324
      omega
    · have hcat := mem_catalogue.mp h
      have hqp' : q ≠ p := fun e => hpcat (e ▸ hcat)
      have hnot : q ∉ S_ht := fun h' => by
        have := (mem_S_ht.mp h').2; have := (catalogueSet_prime hcat).2; omega
      rw [padicValNat_primes hqp', Bp_of_not_mem_S_ht hnot]
      have := padicValNat_multiplier_le_cat hk hcat
      omega
  · intro q hq hqS hv
    have : Fact q.Prime := ⟨hq⟩
    have : Fact p.Prime := ⟨hp⟩
    have hq324 : 324 < q := by
      by_contra h
      exact hqS (mem_S_b.mpr (Or.inl (mem_S_ht.mpr ⟨hq, by omega⟩)))
    have hqcat : q ∉ catalogueSet := fun h => hqS (mem_S_b.mpr (Or.inr (mem_catalogue.mpr h)))
    rw [padicValInt_pattern_value hε hk0 hp,
      padicValNat.eq_zero_of_not_dvd (not_dvd_multiplier hk hq hq324 hqcat), zero_add] at hv ⊢
    by_cases hqp : q = p
    · subst hqp; exact ⟨rfl, by rw [padicValNat_self]⟩
    · rw [padicValNat_primes hqp] at hv; exact absurd rfl hv

/-! ### Valuations of `x / v` -/

theorem padicValRat_div_int {q : ℕ} [Fact q.Prime] {x v : ℤ} (hx : x ≠ 0) (hv : v ≠ 0) :
    padicValRat q ((x : ℚ) / v) = padicValInt q x - padicValInt q v := by
  rw [padicValRat.div (by exact_mod_cast hx) (by exact_mod_cast hv), padicValRat.of_int,
    padicValRat.of_int]

/-- The integer contact values `𝒞 = {0, -15, -20, -24, -30, -60}`. -/
def contactInts : List ℤ := [0, -15, -20, -24, -30, -60]

theorem mem_contactSet_iff {c : ℚ} : c ∈ contactSet ↔ ∃ b ∈ contactInts, c = b := by
  simp [contactSet, contactInts]

theorem contactInts_sub_patternShifts' : ∀ b ∈ contactInts, b ∈ patternShifts := by decide

theorem contactInts_sub_patternShifts {b : ℤ} (hb : b ∈ contactInts) : b ∈ patternShifts :=
  contactInts_sub_patternShifts' b hb

theorem mem_patternValues_v (A u₁ u₂ v : ℤ) : v ∈ patternValues A u₁ u₂ v := List.mem_cons_self

theorem mem_patternValues_u (A u₁ u₂ v : ℤ) {u b : ℤ} (hu : u ∈ [u₁, u₂, A * v - u₁ - u₂])
    (hb : b ∈ patternShifts) : u - b * v ∈ patternValues A u₁ u₂ v := by
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨u, hu, List.mem_map.mpr ⟨b, hb, rfl⟩⟩)

/-! ### The slopes -/

/-- The core of the argument: if `v` and all `u - b v` (`b ∈ 𝒞 ∪ {1}`) satisfy the conclusions of
`pattern_value_spec` with primes `pf x > B₀` that are good, then `u / v` is a good slope. -/
theorem goodSlope_of_values (B₀ : ℝ) (u v : ℤ) (pf : ℤ → ℕ)
    (hval : ∀ x, (x = v ∨ ∃ b ∈ patternShifts, x = u - b * v) →
      x ≠ 0 ∧ (∀ q ∈ S_b, padicValInt q x ≤ Bp q) ∧
      (∀ q : ℕ, q.Prime → q ∉ S_b → padicValInt q x ≠ 0 → q = pf x ∧ padicValInt q x = 1) ∧
      B₀ < pf x ∧ GoodPatternPrime (pf x)) :
    GoodSlope B₀ ((u : ℚ) / v) := by
  classical
  have hv := hval v (Or.inl rfl)
  have hv0 : v ≠ 0 := hv.1
  have hvQ : (v : ℚ) ≠ 0 := by exact_mod_cast hv0
  have hx : ∀ b ∈ patternShifts, _ := fun b hb => hval (u - b * v) (Or.inr ⟨b, hb, rfl⟩)
  -- `t - b = (u - b v) / v`
  have hsub : ∀ b : ℤ, (u : ℚ) / v - b = ((u - b * v : ℤ) : ℚ) / v := by
    intro b; push_cast; field_simp
  have h1 : (1 : ℤ) ∈ patternShifts := by simp [patternShifts]
  have hc : ∀ b ∈ contactInts, b ∈ patternShifts := fun b hb => contactInts_sub_patternShifts hb
  -- valuations of `t - b` at a prime
  have hvt : ∀ (q : ℕ) [Fact q.Prime] (b : ℤ), b ∈ patternShifts →
      padicValRat q ((u : ℚ) / v - b) = padicValInt q (u - b * v) - padicValInt q v := by
    intro q _ b hb
    rw [hsub, padicValRat_div_int (hx b hb).1 hv0]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- condition 1: `t ∉ 𝒞`
    intro hmem
    obtain ⟨b, hb, hbt⟩ := mem_contactSet_iff.mp hmem
    have := (hx b (hc b hb)).1
    apply this
    have h0 : ((u : ℚ) / v - b) = 0 := by rw [hbt]; ring
    rw [hsub] at h0
    exact_mod_cast (div_eq_zero_iff.mp h0).resolve_right hvQ
  · intro h
    have := (hx 1 h1).1
    apply this
    have h0 : ((u : ℚ) / v - (1 : ℤ)) = 0 := by rw [h]; simp
    rw [hsub] at h0
    exact_mod_cast (div_eq_zero_iff.mp h0).resolve_right hvQ
  · -- condition 2
    intro q hq
    have : Fact q.Prime := ⟨prime_of_mem_S_b hq⟩
    have hB : ∀ b ∈ patternShifts, (0 : ℤ) ≤ padicValInt q (u - b * v) ∧
        padicValInt q (u - b * v) ≤ Bp q := fun b hb =>
      ⟨Int.natCast_nonneg _, by exact_mod_cast (hx b hb).2.1 q hq⟩
    have hBv : (0 : ℤ) ≤ padicValInt q v ∧ (padicValInt q v : ℤ) ≤ Bp q :=
      ⟨Int.natCast_nonneg _, by exact_mod_cast hv.2.1 q hq⟩
    constructor
    · have := hvt q 1 h1
      rw [Int.cast_one] at this
      rw [this, abs_le]
      have := hB 1 h1
      constructor <;> linarith
    · -- `F(t)/(t-1)^8 = v² ∏ (u - c v) / (u - v)^8`
      have hF : contactPoly ((u : ℚ) / v) / ((u : ℚ) / v - 1) ^ 8 =
          ((u - 0 * v : ℤ) : ℚ) * ((u - (-15) * v : ℤ) : ℚ) * ((u - (-20) * v : ℤ) : ℚ) *
            ((u - (-24) * v : ℤ) : ℚ) * ((u - (-30) * v : ℤ) : ℚ) *
            ((u - (-60) * v : ℤ) : ℚ) * (v : ℚ) ^ 2 / ((u - 1 * v : ℤ) : ℚ) ^ 8 := by
        have hu1 : ((u - 1 * v : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (hx 1 h1).1
        have hu1' : (u : ℚ) - v ≠ 0 := by push_cast at hu1; simpa using hu1
        rw [show (u : ℚ) / v - 1 = ((u : ℚ) - v) / v by field_simp]
        unfold contactPoly
        push_cast
        field_simp
        ring
      have hmem : ∀ b ∈ ([0, -15, -20, -24, -30, -60, 1] : List ℤ), b ∈ patternShifts :=
        fun b hb => hb
      have n := fun b hb => (hx b (hmem b hb)).1
      have nQ : ∀ b ∈ ([0, -15, -20, -24, -30, -60, 1] : List ℤ), ((u - b * v : ℤ) : ℚ) ≠ 0 :=
        fun b hb => by exact_mod_cast n b hb
      rw [hF, padicValRat.div (by
          refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
            (nQ 0 (by simp)) (nQ (-15) (by simp))) (nQ (-20) (by simp))) (nQ (-24) (by simp)))
            (nQ (-30) (by simp))) (nQ (-60) (by simp))) (pow_ne_zero _ hvQ))
          (pow_ne_zero _ (nQ 1 (by simp))),
        padicValRat.mul (by
          refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
            (nQ 0 (by simp)) (nQ (-15) (by simp))) (nQ (-20) (by simp))) (nQ (-24) (by simp)))
            (nQ (-30) (by simp))) (nQ (-60) (by simp))) (pow_ne_zero _ hvQ),
        padicValRat.mul (by
          refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
            (nQ 0 (by simp)) (nQ (-15) (by simp))) (nQ (-20) (by simp))) (nQ (-24) (by simp)))
            (nQ (-30) (by simp))) (nQ (-60) (by simp)),
        padicValRat.mul (by
          refine mul_ne_zero (mul_ne_zero (mul_ne_zero
            (nQ 0 (by simp)) (nQ (-15) (by simp))) (nQ (-20) (by simp))) (nQ (-24) (by simp)))
            (nQ (-30) (by simp)),
        padicValRat.mul (by
          refine mul_ne_zero (mul_ne_zero
            (nQ 0 (by simp)) (nQ (-15) (by simp))) (nQ (-20) (by simp))) (nQ (-24) (by simp)),
        padicValRat.mul (mul_ne_zero (nQ 0 (by simp)) (nQ (-15) (by simp))) (nQ (-20) (by simp)),
        padicValRat.mul (nQ 0 (by simp)) (nQ (-15) (by simp)),
        padicValRat.pow, padicValRat.pow]
      simp only [padicValRat.of_int]
      have b0 := hB 0 (hmem 0 (by simp))
      have b15 := hB (-15) (hmem (-15) (by simp))
      have b20 := hB (-20) (hmem (-20) (by simp))
      have b24 := hB (-24) (hmem (-24) (by simp))
      have b30 := hB (-30) (hmem (-30) (by simp))
      have b60 := hB (-60) (hmem (-60) (by simp))
      have b1 := hB 1 h1
      rw [abs_le]
      push_cast
      constructor <;> linarith
  · -- condition 3
    intro q hqS hodd
    obtain ⟨hq, c, hcC, hpos, -⟩ := hodd
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨b, hb, rfl⟩ := mem_contactSet_iff.mp hcC
    have hvb := hvt q b (hc b hb)
    have hne : padicValInt q (u - b * v) ≠ 0 := by
      intro h0; rw [hvb, h0] at hpos; push_cast at hpos
      linarith [(Int.natCast_nonneg (padicValInt q v) : (0 : ℤ) ≤ _)]
    obtain ⟨hqe, -⟩ := (hx b (hc b hb)).2.2.1 q hq hqS hne
    rw [hqe]
    refine ⟨(hx b (hc b hb)).2.2.2.1, (hx b (hc b hb)).2.2.2.2.goodSlopePrime, ?_⟩
    rw [← hqe]
    intro c' hc' hpos'
    obtain ⟨b', hb', rfl⟩ := mem_contactSet_iff.mp hc'
    have hvb' := hvt q b' (hc b' hb')
    have hne' : padicValInt q (u - b' * v) ≠ 0 := by
      intro h0; rw [hvb', h0] at hpos'; push_cast at hpos'
      linarith [(Int.natCast_nonneg (padicValInt q v) : (0 : ℤ) ≤ _)]
    have h1' := ((hx b' (hc b' hb')).2.2.1 q hq hqS hne').2
    have hv01 : padicValInt q v = 0 ∨ padicValInt q v = 1 := by
      by_cases h : padicValInt q v = 0
      · exact Or.inl h
      · exact Or.inr (hv.2.2.1 q hq hqS h).2
    rw [hvb', h1'] at hpos' ⊢
    rcases hv01 with h | h
    · rw [h]; norm_num
    · rw [h] at hpos'; norm_num at hpos'
  · -- condition 4
    refine ⟨((contactInts.map fun b => pf (u - b * v)).toFinset).filter
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
        have hvb := hvt q b (hc b hb)
        have hne : padicValInt q (u - b * v) ≠ 0 := by
          intro h0; rw [hvb, h0] at hpos; push_cast at hpos
          linarith [(Int.natCast_nonneg (padicValInt q v) : (0 : ℤ) ≤ _)]
        obtain ⟨hqe, -⟩ := (hx b (hc b hb)).2.2.1 q hq hqS hne
        exact List.mem_map.mpr ⟨b, hb, hqe.symm⟩

/-- **Slopes of an integer from the prime pattern.** Under hypothesis 22P, for every `A ∈ ℤ` and
every real `B₀` there are `t₁, t₂, t₃ ∈ ℚ` with `t₁ + t₂ + t₃ = A`, each satisfying conditions
1-4 (`GoodSlope B₀`). -/
theorem pattern_slopes (h22 : FixedPrimePattern) (A : ℤ) (B₀ : ℝ) :
    ∃ t : Fin 3 → ℚ, ∑ j, t j = A ∧ ∀ j, GoodSlope B₀ (t j) := by
  classical
  set B₀' : ℝ := max B₀ (max 324 (catalogue.sup id : ℕ)) with hB₀'
  obtain ⟨u₁, u₂, v, hv0, hpat⟩ := h22 A B₀'
  have hpat' : ∀ x ∈ patternValues A u₁ u₂ v, ∃ p : ℕ, B₀' < p ∧ GoodPatternPrime p ∧
      ∃ (ε : ℤ) (k : ℕ), (ε = 1 ∨ ε = -1) ∧ k ∈ catalogueMultipliers ∧ x = ε * k * p := by
    intro x hx
    obtain ⟨ε, k, p, hε, hk, hp, hgood, rfl⟩ := hpat x hx
    exact ⟨p, hp, hgood, ε, k, hε, hk, rfl⟩
  choose! pf hpf using hpat'
  -- the facts about every pattern value
  have hfacts : ∀ x ∈ patternValues A u₁ u₂ v,
      x ≠ 0 ∧ (∀ q ∈ S_b, padicValInt q x ≤ Bp q) ∧
      (∀ q : ℕ, q.Prime → q ∉ S_b → padicValInt q x ≠ 0 → q = pf x ∧ padicValInt q x = 1) ∧
      B₀ < pf x ∧ GoodPatternPrime (pf x) := by
    intro x hx
    obtain ⟨hpB, hgood, ε, k, hε, hk, hxe⟩ := hpf x hx
    have hp := hgood.1
    have h324 : (324 : ℝ) < pf x := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hpB
    have hsup : ((catalogue.sup id : ℕ) : ℝ) < pf x :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hpB
    have hp324 : 324 < pf x := by exact_mod_cast h324
    have hpcat : pf x ∉ catalogueSet := fun h => by
      have := le_catalogue_sup h
      have : (pf x : ℝ) ≤ (catalogue.sup id : ℕ) := by exact_mod_cast this
      linarith
    obtain ⟨h1, h2, h3⟩ := pattern_value_spec hε hk hp hp324 hpcat
    rw [← hxe] at h1 h2 h3
    exact ⟨h1, h2, h3, lt_of_le_of_lt (le_max_left _ _) hpB, hgood⟩
  let u : Fin 3 → ℤ := ![u₁, u₂, A * v - u₁ - u₂]
  refine ⟨fun j => (u j : ℚ) / v, ?_, fun j => ?_⟩
  · have hvQ : (v : ℚ) ≠ 0 := by exact_mod_cast hv0
    simp only [Fin.sum_univ_three, u, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    field_simp
    push_cast
    ring
  · have hu : u j ∈ [u₁, u₂, A * v - u₁ - u₂] := by
      fin_cases j <;> simp [u]
    refine goodSlope_of_values B₀ (u j) v pf fun x hx => hfacts x ?_
    rcases hx with rfl | ⟨b, hb, rfl⟩
    · exact mem_patternValues_v A u₁ u₂ x
    · exact mem_patternValues_u A u₁ u₂ v hu hb

/-- **(SR) Slope representation**: every integer is a sum of three rationals satisfying the four
conditions `GoodSlope 0`. This is exactly what completeness uses of the prime-pattern
hypothesis. -/
def SlopeRepresentation : Prop :=
  ∀ A : ℤ, ∃ t : Fin 3 → ℚ, ∑ j, t j = A ∧ ∀ j, GoodSlope 0 (t j)

/-- Hypothesis 22P gives the slope representation (`pattern_slopes` with `B₀ = 0`). -/
theorem slopeRepresentation_of_fixedPrimePattern (h22 : FixedPrimePattern) : SlopeRepresentation :=
  fun A => pattern_slopes h22 A 0

end ZInQ.Mult
