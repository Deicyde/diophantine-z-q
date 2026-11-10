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

end

end ZInQ.Density
