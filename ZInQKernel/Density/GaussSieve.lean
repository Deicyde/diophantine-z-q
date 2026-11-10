import ZInQKernel.Density.GaussSieve.Instance
import ZInQKernel.Density.Description

/-!
# The uniform bound for the primes bad at a medium prime `ℓ` (pd-paper.md §4.3–4.5)

`GaussBad ℓ` is the set of primes `p = c² + e²` with `ℓ ∣ c` and `ℓ ∣ p + 1`. By Proposition 1.6
(`exists_sq_add_sq`, file `Density/Description.lean`), every prime of the note's `BadSet ℓ`
(`p` prime, `InClass p`, `ℓ ∣ c_p`, `ℓ ∣ p + 1`) lies in `GaussBad ℓ`.

* `card_gaussBad_le`: for `N`, `w ≥ 2` and a prime `ℓ ≥ 5`, with `K = ⌊√N⌋/ℓ`,
  `#(GaussBad ℓ ∩ [0, N]) ≤ (w + 1) + 2·(10(2K + 1)(2K + 2)/log w + w⁸(4K + 4))`.
  This is (4.1) + the Selberg bound (§4.4) + Lemma 4.5 (`S ≥ log w / 10`), summed over the (at most
  two) roots `b` of `b² = -1` mod `ℓ`.
* `uniformGaussBadBound`: Proposition 4.2 with `A = 14402`, for `N ≥ N₁`, with `w = ⌊N^{1/40}⌋`.
* `uniformBadBound`: the same for the note's `BadSet`, in the form of `UniformBadBound` (§6.1).
-/

open Finset

namespace ZInQ.Density

open GaussSieve

noncomputable section

open scoped Classical

/-- Primes `p = c² + e²` with `ℓ ∣ c` and `ℓ ∣ p + 1`. -/
def GaussBad (ℓ : ℕ) : Set ℕ :=
  {p | p.Prime ∧ ∃ c e : ℤ, (p : ℤ) = c ^ 2 + e ^ 2 ∧ (ℓ : ℤ) ∣ c ∧ ℓ ∣ p + 1}

/-- The note's bad set at `ℓ` lies in `GaussBad ℓ` (Proposition 1.6). -/
theorem mem_gaussBad_of_bad {ℓ p : ℕ} (hp : p.Prime) (hC : InClass p) (h1 : (ℓ : ℤ) ∣ cp p)
    (h2 : ℓ ∣ p + 1) : p ∈ GaussBad ℓ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, he⟩ := exists_sq_add_sq hC
  exact ⟨hp, cp p, e, he, h1, h2⟩

/-- At most two square roots of `-1` modulo a prime. -/
theorem card_sqrt_neg_one_le (ℓ : ℕ) [Fact ℓ.Prime] :
    #((univ : Finset (ZMod ℓ)).filter (fun z : ZMod ℓ => z ^ 2 = (-1 : ZMod ℓ))) ≤ 2 := by
  set R := (univ : Finset (ZMod ℓ)).filter (fun z : ZMod ℓ => z ^ 2 = (-1 : ZMod ℓ))
  rcases R.eq_empty_or_nonempty with h | ⟨z₀, hz₀⟩
  · rw [h]; simp
  · have hz₀' : z₀ ^ 2 = -1 := (mem_filter.1 hz₀).2
    have hsub : R ⊆ {z₀, -z₀} := by
      intro z hz
      have hz' : z ^ 2 = -1 := (mem_filter.1 hz).2
      have : (z - z₀) * (z + z₀) = 0 := by linear_combination hz' - hz₀'
      rcases mul_eq_zero.1 this with h | h
      · simp [sub_eq_zero.1 h]
      · simp [eq_neg_of_add_eq_zero_left h]
    exact (card_le_card hsub).trans (card_insert_le _ _)

theorem one_le_weights {ℓ : ℕ} {b : ℤ} {K w : ℕ} {hw : 1 ≤ w} {n : ℕ}
    (hn : n ∈ (gaussSieve ℓ b K w hw).support) : 1 ≤ (gaussSieve ℓ b K w hw).weights n := by
  simp only [gaussSieve, mem_image] at hn ⊢
  obtain ⟨x, hx, rfl⟩ := hn
  have : 0 < #((gsBox K).filter (fun y => gsF ℓ b y = gsF ℓ b x)) :=
    card_pos.2 ⟨x, mem_filter.2 ⟨hx, rfl⟩⟩
  exact_mod_cast this

/-- The primes `> w` of the support are counted by the sifted sum. -/
theorem card_support_primes_le_siftedSum {ℓ : ℕ} {b : ℤ} {K w : ℕ} {hw : 1 ≤ w} :
    (#((gaussSieve ℓ b K w hw).support.filter (fun n => n.Prime ∧ w < n)) : ℝ) ≤
      (gaussSieve ℓ b K w hw).siftedSum := by
  rw [BoundingSieve.siftedSum, card_filter, Nat.cast_sum]
  refine sum_le_sum fun n hn => ?_
  by_cases h1 : n.Prime ∧ w < n
  · have hcop : Nat.Coprime (gaussSieve ℓ b K w hw).prodPrimes n := by
      simp only [gaussSieve]
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd h1.1).2 fun hd => ?_)
      have := (mem_gsPrimes.1 (mem_gsPrimes_of_dvd h1.1 hd)).1
      omega
    rw [if_pos h1, if_pos hcop]
    simpa using one_le_weights hn
  · rw [if_neg h1]
    split_ifs
    · simp only [Nat.cast_zero]; exact BoundingSieve.weights_nonneg _ _
    · simp

/-- A point of `GaussBad ℓ ∩ (w, N]` lies in the support of the sieve for `b = e mod ℓ`. -/
theorem mem_support_of_gaussBad {ℓ : ℕ} [hℓ' : Fact ℓ.Prime] {N w p : ℕ} (hw : 1 ≤ w)
    (hpN : p ≤ N) (hpw : w < p) (hp : p ∈ GaussBad ℓ) :
    ∃ b ∈ (univ : Finset (ZMod ℓ)).filter (fun z : ZMod ℓ => z ^ 2 = (-1 : ZMod ℓ)),
      p ∈ ((gaussSieve ℓ (b.val : ℤ) (Nat.sqrt N / ℓ) w hw).support.filter
        (fun n => n.Prime ∧ w < n)) := by
  have hℓ := hℓ'.out
  obtain ⟨hpp, c, e, hpce, hc, hp1⟩ := hp
  obtain ⟨U, rfl⟩ := hc
  set b : ZMod ℓ := (e : ZMod ℓ)
  have hb2 : b ^ 2 = -1 := by
    have h1 : ((p + 1 : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hp1
    have h2 : ((p : ℤ) : ZMod ℓ) = (((ℓ : ℤ) * U) ^ 2 + e ^ 2 : ℤ) := by rw [hpce]
    push_cast at h1 h2
    simp only [ZMod.natCast_self, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_add] at h2
    simp only [b]
    linear_combination h2.symm + h1
  obtain ⟨V, hV⟩ : (ℓ : ℤ) ∣ e - (b.val : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simp [b]
  have hev : e = (b.val : ℤ) + ℓ * V := by linarith
  refine ⟨b, mem_filter.2 ⟨mem_univ _, hb2⟩, mem_filter.2 ⟨?_, hpp, hpw⟩⟩
  simp only [gaussSieve, mem_image]
  refine ⟨(U, V), ?_, ?_⟩
  · -- the box conditions
    set T := Nat.sqrt N
    set K := T / ℓ
    have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast hℓ.pos
    have hTK : (T : ℤ) < ℓ * (K + 1) := by exact_mod_cast Nat.lt_mul_div_succ T hℓ.pos
    have hsq : ∀ z : ℤ, z ^ 2 ≤ N → |z| ≤ T := by
      intro z hz
      have : z.natAbs ^ 2 ≤ N := by
        have : ((z.natAbs ^ 2 : ℕ) : ℤ) ≤ N := by push_cast; rw [sq_abs]; exact hz
        exact_mod_cast this
      have := Nat.le_sqrt'.2 this
      rw [Int.abs_eq_natAbs]; exact_mod_cast this
    have hpN' : (p : ℤ) ≤ N := by exact_mod_cast hpN
    have hc2 : |(ℓ : ℤ) * U| ≤ T := hsq _ (by nlinarith [sq_nonneg e])
    have he2 : |e| ≤ T := hsq _ (by nlinarith [sq_nonneg ((ℓ : ℤ) * U)])
    have hbv : (b.val : ℤ) < ℓ := by exact_mod_cast ZMod.val_lt b
    have hbv0 : (0 : ℤ) ≤ b.val := by positivity
    rw [abs_le] at hc2 he2
    simp only [gsBox, GaussSieve.box, mem_product, mem_Ico]
    push_cast
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · -- -K ≤ U
      by_contra h
      have : (ℓ : ℤ) * U < ℓ * (-(K : ℤ)) - ℓ + ℓ := by nlinarith
      nlinarith
    · -- U < K + 1
      by_contra h
      have : (ℓ : ℤ) * (K + 1) ≤ ℓ * U := by nlinarith
      linarith
    · -- -K - 1 ≤ V
      by_contra h
      have : (ℓ : ℤ) * V + ℓ * (K + 2) ≤ 0 := by nlinarith
      nlinarith
    · -- V < K + 1
      by_contra h
      have : (ℓ : ℤ) * (K + 1) ≤ ℓ * V := by nlinarith
      linarith
  · simp only [gsF, gaussFZ]
    rw [← hev, ← hpce]
    simp

/-- **Counting.** `(4.1)` with the Selberg bound and Lemma 4.5, summed over both roots `b`. -/
theorem card_gaussBad_le {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) (N w : ℕ) (hw : 2 ≤ w) :
    (#((range (N + 1)).filter (· ∈ GaussBad ℓ)) : ℝ) ≤
      (w + 1) + 2 * (10 * ((2 * (Nat.sqrt N / ℓ : ℕ) + 1) * (2 * (Nat.sqrt N / ℓ : ℕ) + 2) : ℝ) /
        Real.log w + (w : ℝ) ^ 8 * (4 * (Nat.sqrt N / ℓ : ℕ) + 4)) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hw1 : 1 ≤ w := by omega
  set K := Nat.sqrt N / ℓ
  set R := (univ : Finset (ZMod ℓ)).filter (fun z : ZMod ℓ => z ^ 2 = (-1 : ZMod ℓ))
  set B : ℝ := 10 * ((2 * K + 1) * (2 * K + 2) : ℝ) / Real.log w + (w : ℝ) ^ 8 * (4 * K + 4)
  let Sb : ZMod ℓ → Finset ℕ := fun b =>
    (gaussSieve ℓ (b.val : ℤ) K w hw1).support.filter (fun n => n.Prime ∧ w < n)
  have hsub : (range (N + 1)).filter (· ∈ GaussBad ℓ) ⊆ range (w + 1) ∪ R.biUnion Sb := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    rcases le_or_gt p w with h | h
    · exact mem_union_left _ (mem_range.2 (by omega))
    · obtain ⟨b, hb, hpb⟩ := mem_support_of_gaussBad (N := N) hw1 (by omega) h hp.2
      exact mem_union_right _ (mem_biUnion.2 ⟨b, hb, hpb⟩)
  have hlogw : 0 < Real.log w := Real.log_pos (by exact_mod_cast hw)
  have hSb : ∀ b ∈ R, (#(Sb b) : ℝ) ≤ B := by
    intro b _
    have h1 := card_support_primes_le_siftedSum (ℓ := ℓ) (b := (b.val : ℤ)) (K := K) (hw := hw1)
    have h2 := siftedSum_le (b := (b.val : ℤ)) (K := K) (hw := hw1) hℓ
    have h3 := selbergBoundingSum_ge_log (b := (b.val : ℤ)) (K := K) (hw := hw1) hℓ hℓ5
    have hX : (0 : ℝ) ≤ (2 * K + 1) * (2 * K + 2) := by positivity
    have h4 : ((2 * K + 1) * (2 * K + 2) : ℝ) / (gaussSieve ℓ (b.val : ℤ) K w hw1).selbergBoundingSum
        ≤ 10 * ((2 * K + 1) * (2 * K + 2) : ℝ) / Real.log w := by
      rw [show 10 * ((2 * K + 1) * (2 * K + 2) : ℝ) / Real.log w =
        ((2 * K + 1) * (2 * K + 2) : ℝ) / (Real.log w / 10) by field_simp]
      exact div_le_div_of_nonneg_left hX (by positivity) h3
    simp only [Sb, B]
    linarith
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  have hcard2 : (#(R.biUnion Sb) : ℝ) ≤ 2 * B := by
    calc (#(R.biUnion Sb) : ℝ) ≤ ∑ b ∈ R, (#(Sb b) : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ b ∈ R, B := sum_le_sum hSb
      _ = #R * B := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 * B := by
        have hB : 0 ≤ B := by
          have := hSb
          positivity
        have h2 : (#R : ℝ) ≤ 2 := by
          have h := card_sqrt_neg_one_le ℓ
          rw [← Nat.cast_ofNat, Nat.cast_le]; exact h
        exact mul_le_mul_of_nonneg_right h2 hB
  have : (#((range (N + 1)).filter (· ∈ GaussBad ℓ)) : ℝ) ≤ (w + 1 : ℕ) + #(R.biUnion Sb) := by
    rw [← card_range (w + 1)]; exact_mod_cast hcard
  push_cast at this
  linarith

/-- The test case `ℓ = 5` of the sieve instance: the Selberg bound and `S ≥ (log w)/10`. -/
theorem siftedSum_le_five (b : ℤ) (K w : ℕ) (hw : 1 ≤ w) :
    (gaussSieve 5 b K w hw).siftedSum ≤
        ((2 * K + 1) * (2 * K + 2) : ℝ) / (gaussSieve 5 b K w hw).selbergBoundingSum +
          (w : ℝ) ^ 8 * (4 * K + 4) ∧
      Real.log w / 10 ≤ (gaussSieve 5 b K w hw).selbergBoundingSum :=
  ⟨siftedSum_le Nat.prime_five, selbergBoundingSum_ge_log Nat.prime_five le_rfl⟩

/-- The real inequality behind Proposition 4.2, with `u = N^{1/40}`. -/
theorem gaussBad_final_ineq {u ℓ : ℝ} {K w : ℕ} (hu4 : 4 ≤ u) (hlog : 400 * Real.log u ≤ u ^ 2)
    (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ^ 4 ≤ u ^ 40) (hK : (K : ℝ) ≤ u ^ 20 / ℓ) (hw1 : (w : ℝ) ≤ u)
    (hw2 : u - 1 < w) :
    (w + 1) + 2 * (10 * ((2 * K + 1) * (2 * K + 2) : ℝ) / Real.log w + (w : ℝ) ^ 8 * (4 * K + 4))
      ≤ 14402 * u ^ 40 / (ℓ ^ 2 * Real.log (u ^ 40)) := by
  have hu0 : 0 < u := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ10 : ℓ ≤ u ^ 10 := by
    rw [show u ^ 40 = (u ^ 10) ^ 4 by ring] at hℓ
    exact (pow_le_pow_iff_left₀ hℓ0.le (by positivity) (by norm_num)).1 hℓ
  have hℓ20 : ℓ ^ 2 ≤ u ^ 20 := by
    calc ℓ ^ 2 ≤ (u ^ 10) ^ 2 := pow_le_pow_left₀ hℓ0.le hℓ10 2
      _ = u ^ 20 := by ring
  have hu1 : 1 ≤ u := by linarith
  have hu10 : u ≤ u ^ 10 := le_self_pow₀ hu1 (by norm_num)
  set Q := u ^ 20 / ℓ with hQ
  have hQ10 : u ^ 10 ≤ Q := by
    rw [hQ, le_div_iff₀ hℓ0]
    calc u ^ 10 * ℓ ≤ u ^ 10 * u ^ 10 := mul_le_mul_of_nonneg_left hℓ10 (by positivity)
      _ = u ^ 20 := by ring
  have hQ4 : 4 ≤ Q := by linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hX : ((2 * K + 1) * (2 * K + 2) : ℝ) ≤ 9 * Q ^ 2 := by nlinarith
  have hE : (4 * K + 4 : ℝ) ≤ 5 * Q := by linarith
  have hlogu : Real.log 4 ≤ Real.log u := Real.log_le_log (by norm_num) hu4
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlu0 : 0 < Real.log u := by linarith
  have hw0 : (0 : ℝ) < w := by linarith
  have hlogw : Real.log u / 2 ≤ Real.log w := by
    have h1 : u / 2 ≤ w := by linarith
    have h2 : Real.log (u / 2) ≤ Real.log w := Real.log_le_log (by positivity) h1
    rw [Real.log_div hu0.ne' (by norm_num)] at h2
    linarith
  set D := u ^ 40 / (ℓ ^ 2 * Real.log u) with hD
  have hDpos : 0 < D := by positivity
  have hL : Real.log (u ^ 40) = 40 * Real.log u := by rw [Real.log_pow]; norm_num
  have hRHS : 14402 * u ^ 40 / (ℓ ^ 2 * Real.log (u ^ 40)) = (14402 / 40) * D := by
    rw [hL, hD]; field_simp
  rw [hRHS]
  -- main term
  have ha : 10 * ((2 * K + 1) * (2 * K + 2) : ℝ) / Real.log w ≤ 180 * D := by
    calc 10 * ((2 * K + 1) * (2 * K + 2) : ℝ) / Real.log w ≤ 10 * (9 * Q ^ 2) / (Real.log u / 2) :=
          div_le_div₀ (by positivity) (by linarith) (by positivity) hlogw
      _ = 180 * D := by rw [hQ, hD]; field_simp; ring
  -- error term
  have hb : (w : ℝ) ^ 8 * (4 * K + 4) ≤ D / 80 := by
    have hw8 : (w : ℝ) ^ 8 ≤ u ^ 8 := pow_le_pow_left₀ hw0.le hw1 8
    have h1 : (w : ℝ) ^ 8 * (4 * K + 4) ≤ u ^ 8 * (5 * Q) :=
      mul_le_mul hw8 hE (by positivity) (by positivity)
    refine h1.trans ?_
    have h2 : 400 * ℓ * u ^ 28 * Real.log u ≤ u ^ 40 := by
      calc 400 * ℓ * u ^ 28 * Real.log u = ℓ * u ^ 28 * (400 * Real.log u) := by ring
        _ ≤ u ^ 10 * u ^ 28 * u ^ 2 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hℓ10 (by positivity)) hlog (by positivity)
            (by positivity)
        _ = u ^ 40 := by ring
    rw [hQ, hD, show u ^ 8 * (5 * (u ^ 20 / ℓ)) = 5 * u ^ 28 / ℓ by ring,
      show u ^ 40 / (ℓ ^ 2 * Real.log u) / 80 = u ^ 40 / (80 * ℓ ^ 2 * Real.log u) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    calc 5 * u ^ 28 * (80 * ℓ ^ 2 * Real.log u) = (400 * ℓ * u ^ 28 * Real.log u) * ℓ := by ring
      _ ≤ u ^ 40 * ℓ := mul_le_mul_of_nonneg_right h2 hℓ0.le
  -- the primes `≤ w`
  have hc : (w : ℝ) + 1 ≤ D / 40 := by
    have h1 : (w : ℝ) + 1 ≤ 2 * u := by linarith
    refine h1.trans ?_
    rw [hD, div_div, le_div_iff₀ (by positivity)]
    have h80 : 80 * Real.log u ≤ u ^ 2 := by linarith
    have hu23 : u ^ 23 ≤ u ^ 40 := pow_le_pow_right₀ hu1 (by norm_num)
    calc 2 * u * (ℓ ^ 2 * Real.log u * 40) = u * ℓ ^ 2 * (80 * Real.log u) := by ring
      _ ≤ u * u ^ 20 * u ^ 2 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hℓ20 hu0.le) h80 (by positivity) (by positivity)
      _ = u ^ 23 := by ring
      _ ≤ u ^ 40 := hu23
  linarith

/-- **Proposition 4.2** for `GaussBad` (constant `A = 14402`, `N₁` not explicit). -/
theorem uniformGaussBadBound :
    ∃ A N₁ : ℝ, 0 < A ∧ ∀ N : ℕ, N₁ ≤ N → ∀ ℓ : ℕ, ℓ.Prime → ℓ % 4 = 1 → 5 ≤ ℓ →
      ((ℓ : ℝ) ^ 4 ≤ N) →
      (((range (N + 1)).filter (· ∈ GaussBad ℓ)).card : ℝ) ≤ A * N / (ℓ ^ 2 * Real.log N) := by
  have hev : ∀ᶠ u : ℝ in Filter.atTop, 400 * Real.log u ≤ u ^ 2 := by
    have h := (isLittleO_log_rpow_atTop (r := 2) (by norm_num)).bound
      (show (0 : ℝ) < 1 / 400 by norm_num)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with u hu hu1
    rw [Real.norm_of_nonneg (Real.log_nonneg hu1), Real.norm_of_nonneg (by positivity),
      Real.rpow_two] at hu
    linarith
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.1 hev
  set M := max U₀ 4
  refine ⟨14402, M ^ 40, by norm_num, fun N hN ℓ hℓ _ hℓ5 hℓN => ?_⟩
  have hM4 : 4 ≤ M := le_max_right _ _
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set u := (N : ℝ) ^ (((40 : ℕ) : ℝ)⁻¹) with hu
  have hu40 : u ^ 40 = N := Real.rpow_inv_natCast_pow hn0 (by norm_num)
  have huM : M ≤ u := by
    have := Real.rpow_le_rpow (by positivity) hN (show (0 : ℝ) ≤ ((40 : ℕ) : ℝ)⁻¹ by positivity)
    rwa [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)] at this
  have hu4 : 4 ≤ u := hM4.trans huM
  have hlog : 400 * Real.log u ≤ u ^ 2 := hU₀ u ((le_max_left _ _).trans huM)
  set w := ⌊u⌋₊
  have hw1 : (w : ℝ) ≤ u := Nat.floor_le (by linarith)
  have hw2 : u - 1 < w := Nat.sub_one_lt_floor u
  have hw : 2 ≤ w := by
    have : (2 : ℝ) < w := by linarith
    exact_mod_cast this.le
  have hsqrt : √(N : ℝ) = u ^ 20 := by
    rw [← hu40, show u ^ 40 = (u ^ 20) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.one_lt.le
  have hK : ((Nat.sqrt N / ℓ : ℕ) : ℝ) ≤ u ^ 20 / ℓ := by
    refine Nat.cast_div_le.trans ?_
    rw [← hsqrt]
    exact div_le_div_of_nonneg_right Real.nat_sqrt_le_real_sqrt (by positivity)
  have h1 := card_gaussBad_le hℓ hℓ5 N w hw
  have h2 := gaussBad_final_ineq hu4 hlog hℓR (by rw [hu40]; exact hℓN) hK hw1 hw2
  rw [hu40] at h2
  linarith

/-- **`uniformBadBound`** (pd-paper.md §6.1, file 8): the statement `UniformBadBound`, with
`BadSet ℓ = {p | p.Prime ∧ InClass p ∧ (ℓ : ℤ) ∣ cp p ∧ ℓ ∣ p + 1}` written out. -/
theorem uniformBadBound :
    ∃ A N₁ : ℝ, 0 < A ∧ ∀ N : ℕ, N₁ ≤ N → ∀ ℓ : ℕ, ℓ.Prime → ℓ % 4 = 1 → 5 ≤ ℓ →
      ((ℓ : ℝ) ^ 4 ≤ N) →
      (((Finset.range (N + 1)).filter
          (· ∈ {p : ℕ | p.Prime ∧ InClass p ∧ (ℓ : ℤ) ∣ cp p ∧ ℓ ∣ p + 1})).card : ℝ) ≤
        A * N / (ℓ ^ 2 * Real.log N) := by
  obtain ⟨A, N₁, hA, h⟩ := uniformGaussBadBound
  refine ⟨A, N₁, hA, fun N hN ℓ hℓ h4 h5 hℓN => le_trans ?_ (h N hN ℓ hℓ h4 h5 hℓN)⟩
  have hsub : (Finset.range (N + 1)).filter
        (· ∈ {p : ℕ | p.Prime ∧ InClass p ∧ (ℓ : ℤ) ∣ cp p ∧ ℓ ∣ p + 1}) ⊆
      (range (N + 1)).filter (· ∈ GaussBad ℓ) := by
    intro p hp
    simp only [mem_filter, Set.mem_setOf_eq] at hp ⊢
    exact ⟨hp.1, mem_gaussBad_of_bad hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2⟩
  exact_mod_cast card_le_card hsub

end

end ZInQ.Density
