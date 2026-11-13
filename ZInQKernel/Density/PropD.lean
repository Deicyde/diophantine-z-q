import ZInQKernel.Density.Abel
import ZInQKernel.Density.Residues
import ZInQKernel.Density.PrimeTail
import ZInQKernel.Density.Lattice

/-!
# Proposition D modulo the uniform bad-prime bound (pd-paper §5, Theorem D; §6.1 file 9)

* `BadSet ℓ` (§2.1): the class primes `p` with `ℓ ∣ c_p` and `ℓ ∣ p + 1`;
* `UniformBadBound` (Proposition 4.2, as a hypothesis): there are `A > 0` and `N₁` with
  `#(Bad_ℓ ∩ [0, N]) ≤ A N/(ℓ² log N)` for all `N ≥ N₁` and all primes `ℓ ≡ 1 (mod 4)` with
  `5 ≤ ℓ` and `ℓ⁴ ≤ N`;
* `goodSlopePrime_of_mem_CL` (Lemma 2.1): `G*_L = C_L ∖ T_L ⊆ G`;
* `card_TL_le`: `#(T_L ∩ [0, N]) ≤ α_L N/log N + 20 N^{3/4}` with `α_L = 3 A log 4/(L log L)`;
* `goodPrimeDensity_of_uniformBadBound` (Theorem D and Proposition 5.3):
  `UniformBadBound → GoodPrimeDensity`.
-/

namespace ZInQ.Density

open Finset Filter

/-- `Bad_ℓ` (§2.1): the primes `p` of the class of Proposition 1.6 with `ℓ ∣ c_p` and
`ℓ ∣ p + 1`. -/
def BadSet (ℓ : ℕ) : Set ℕ := {p | p.Prime ∧ InClass p ∧ (ℓ : ℤ) ∣ cp p ∧ ℓ ∣ p + 1}

theorem badSet_eq (ℓ : ℕ) : BadSet ℓ = BadSetOf cp ℓ := rfl

open Classical in
/-- **The uniform bad-prime bound** (Proposition 4.2 of the note, here a hypothesis): there are
`A > 0` and `N₁` such that for every `N ≥ N₁` and every prime `ℓ ≡ 1 (mod 4)` with `5 ≤ ℓ` and
`ℓ⁴ ≤ N`, `#(Bad_ℓ ∩ [0, N]) ≤ A N / (ℓ² log N)`. -/
def UniformBadBound : Prop :=
  ∃ A N₁ : ℝ, 0 < A ∧ ∀ N : ℕ, N₁ ≤ N → ∀ ℓ : ℕ, ℓ.Prime → ℓ % 4 = 1 → 5 ≤ ℓ →
    ((ℓ : ℝ) ^ 4 ≤ N) →
    (((Finset.range (N + 1)).filter (· ∈ BadSet ℓ)).card : ℝ) ≤ A * N / (ℓ ^ 2 * Real.log N)

/-- `p = c_p² + e²` for class primes (pd-lean-1's `exists_sq_add_sq`). -/
theorem cp_rep : ∀ p : ℕ, p.Prime → InClass p → ∃ e : ℤ, (p : ℤ) = cp p ^ 2 + e ^ 2 :=
  fun p hp hC => by
    have : Fact p.Prime := ⟨hp⟩
    exact exists_sq_add_sq hC

/-- `T_L`: the primes bad at some prime `ℓ > L` with `ℓ ≡ 1 (mod 4)`. -/
def TL (L : ℕ) : Set ℕ := {p | ∃ ℓ : ℕ, ℓ.Prime ∧ L < ℓ ∧ ℓ % 4 = 1 ∧ p ∈ BadSet ℓ}

theorem TL_subset_primes (L : ℕ) : TL L ⊆ {p | p.Prime} := fun _ ⟨_, _, _, _, h⟩ => h.1

theorem goodSlopePrimes_subset_primes : {p | GoodSlopePrime p} ⊆ {p | p.Prime} :=
  fun _ h => h.1

/-- **Lemma 2.1.** `G*_L = C_L ∖ T_L` consists of good slope primes. -/
theorem goodSlopePrime_of_mem_CL {L p : ℕ} (hC : p ∈ CL L) (hT : p ∉ TL L) :
    GoodSlopePrime p := by
  obtain ⟨hp, hcl, hQ⟩ := mem_CL hC
  refine goodSlopePrime_of_gcd hp hcl ?_
  by_contra hg
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hg
  have h1 : (q : ℤ) ∣ cp p := (Int.natCast_dvd_natCast.2 hqd).trans (Int.gcd_dvd_left _ _)
  have h2' : (q : ℤ) ∣ ((p + 1 : ℕ) : ℤ) := by
    have := (Int.natCast_dvd_natCast.2 hqd).trans (Int.gcd_dvd_right (cp p) ((p : ℤ) + 1))
    exact_mod_cast this
  have h2 : q ∣ p + 1 := Int.natCast_dvd_natCast.1 h2'
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : Fact p.Prime := ⟨hp⟩
    have := cp_odd hcl
    omega
  have hq4 := mod_four_of_dvd_cp hq hq2 hp hcl h1 h2
  have hq5 : 5 ≤ q := by
    have := hq.two_le
    omega
  by_cases hqL : q ≤ L
  · exact hQ q (mem_QL.2 ⟨hq5, hqL, hq, hq4⟩) h2
  · exact hT ⟨q, hq, by omega, hq4, hp, hcl, h1, h2⟩

open Classical in
/-- **The count of `T_L`.** Under the uniform bound, for `N ≥ max(N₁, 2)`,
`#(T_L ∩ [0, N]) ≤ α_L N / log N + 20 N^{3/4}` with `α_L = A · 3 log 4/(L log L)`. -/
theorem card_TL_le {A N₁ : ℝ} (hA : 0 < A)
    (hU : ∀ N : ℕ, N₁ ≤ N → ∀ ℓ : ℕ, ℓ.Prime → ℓ % 4 = 1 → 5 ≤ ℓ → ((ℓ : ℝ) ^ 4 ≤ N) →
      (((Finset.range (N + 1)).filter (· ∈ BadSet ℓ)).card : ℝ) ≤ A * N / (ℓ ^ 2 * Real.log N))
    {L : ℕ} (hL : 5 ≤ L) {N : ℕ} (hN : N₁ ≤ N) (hN2 : 2 ≤ N) :
    (((range (N + 1)).filter (· ∈ TL L)).card : ℝ) ≤
      A * (3 * Real.log 4 / (L * Real.log L)) * N / Real.log N + 20 * (N : ℝ) ^ ((3 : ℝ) / 4) := by
  set F := (range (N + 2)).filter (fun ℓ => ℓ.Prime ∧ L < ℓ ∧ ℓ % 4 = 1) with hF
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hsub : (range (N + 1)).filter (· ∈ TL L) ⊆
      F.biUnion (fun ℓ => (range (N + 1)).filter (· ∈ BadSet ℓ)) := by
    intro p hp
    obtain ⟨hpN, ℓ, hℓ, hLℓ, h4, hB⟩ := mem_filter.1 hp
    refine mem_biUnion.2 ⟨ℓ, mem_filter.2 ⟨mem_range.2 ?_, hℓ, hLℓ, h4⟩, mem_filter.2 ⟨hpN, hB⟩⟩
    have := Nat.le_of_dvd (by omega) hB.2.2.2
    have := mem_range.1 hpN
    omega
  have hcard : (((range (N + 1)).filter (· ∈ TL L)).card : ℝ) ≤
      ∑ ℓ ∈ F, (((range (N + 1)).filter (· ∈ BadSet ℓ)).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    exact_mod_cast this
  rw [← sum_filter_add_sum_filter_not F (fun ℓ => ℓ ^ 4 ≤ N)] at hcard
  -- small `ℓ`: the uniform bound
  have hsmall : ∑ ℓ ∈ F.filter (fun ℓ => ℓ ^ 4 ≤ N),
      (((range (N + 1)).filter (· ∈ BadSet ℓ)).card : ℝ) ≤
      A * (3 * Real.log 4 / (L * Real.log L)) * N / Real.log N := by
    have hmem : ∀ ℓ ∈ F.filter (fun ℓ => ℓ ^ 4 ≤ N), ℓ.Prime ∧ L < ℓ ∧ ℓ % 4 = 1 ∧ ℓ ^ 4 ≤ N :=
      fun ℓ hℓ => by
        obtain ⟨h1, h2⟩ := mem_filter.1 hℓ
        obtain ⟨-, h3, h4, h5⟩ := mem_filter.1 h1
        exact ⟨h3, h4, h5, h2⟩
    calc ∑ ℓ ∈ F.filter (fun ℓ => ℓ ^ 4 ≤ N), (((range (N + 1)).filter (· ∈ BadSet ℓ)).card : ℝ)
        ≤ ∑ ℓ ∈ F.filter (fun ℓ => ℓ ^ 4 ≤ N), A * N / ((ℓ : ℝ) ^ 2 * Real.log N) := by
          refine sum_le_sum fun ℓ hℓ => ?_
          obtain ⟨h1, h2, h3, h4⟩ := hmem ℓ hℓ
          exact hU N hN ℓ h1 h3 (by omega) (by exact_mod_cast h4)
      _ = (A * N / Real.log N) * ∑ ℓ ∈ F.filter (fun ℓ => ℓ ^ 4 ≤ N), (1 : ℝ) / (ℓ : ℝ) ^ 2 := by
          rw [mul_sum]
          refine sum_congr rfl fun ℓ _ => ?_
          field_simp
      _ ≤ (A * N / Real.log N) * (3 * Real.log 4 / (L * Real.log L)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact sum_inv_sq_le_of_primes_gt (by omega) _ fun ℓ hℓ =>
            ⟨(hmem ℓ hℓ).1, (hmem ℓ hℓ).2.1⟩
      _ = A * (3 * Real.log 4 / (L * Real.log L)) * N / Real.log N := by ring
  -- large `ℓ`: the lattice count
  have hlarge : ∑ ℓ ∈ F.filter (fun ℓ => ¬ ℓ ^ 4 ≤ N),
      (((range (N + 1)).filter (· ∈ BadSet ℓ)).card : ℝ) ≤ 20 * (N : ℝ) ^ ((3 : ℝ) / 4) := by
    refine sum_card_badSet_large_le cp cp_rep (by omega) _ fun ℓ hℓ => ?_
    obtain ⟨h1, h2⟩ := mem_filter.1 hℓ
    exact ⟨(mem_filter.1 h1).2.1, by omega⟩
  linarith

/-- An eventual comparison: `20 N^{3/4} log N ≤ ε N` for large `N`. -/
theorem eventually_rpow_mul_log_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 20 * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log N ≤ ε * N := by
  have h := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 4) (by norm_num)).bound
    (c := ε / 20) (by positivity)
  have h' := tendsto_natCast_atTop_atTop.eventually (h.and (eventually_ge_atTop (1 : ℝ)))
  filter_upwards [h'] with N ⟨hN, hN1⟩
  have hl : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hp : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  rw [Real.norm_of_nonneg hl, Real.norm_of_nonneg hp] at hN
  have hsplit : (N : ℝ) = (N : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add (by linarith), show (3 : ℝ) / 4 + 1 / 4 = 1 by norm_num, Real.rpow_one]
  have h34 : 0 ≤ (N : ℝ) ^ ((3 : ℝ) / 4) := by positivity
  calc 20 * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log N
      ≤ 20 * (N : ℝ) ^ ((3 : ℝ) / 4) * (ε / 20 * (N : ℝ) ^ ((1 : ℝ) / 4)) := by gcongr
    _ = ε * ((N : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ ((1 : ℝ) / 4)) := by ring
    _ = ε * N := by rw [← hsplit]

/-- A large enough `L`: `L ≥ 5` and `log L ≥ 16 A log 4`. -/
theorem exists_L (A : ℝ) : ∃ L : ℕ, 5 ≤ L ∧ 16 * A * Real.log 4 ≤ Real.log L := by
  refine ⟨max 5 ⌈Real.exp (16 * A * Real.log 4)⌉₊, le_max_left _ _, ?_⟩
  have h1 : Real.exp (16 * A * Real.log 4) ≤ (max 5 ⌈Real.exp (16 * A * Real.log 4)⌉₊ : ℕ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  calc 16 * A * Real.log 4 = Real.log (Real.exp (16 * A * Real.log 4)) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos _) h1

/-- **Proposition D, conditional (Theorem D with Proposition 5.3).** The uniform bad-prime bound
implies that the good slope primes have positive relative upper density in the primes. -/
theorem goodPrimeDensity_of_uniformBadBound (h : UniformBadBound) : GoodPrimeDensity := by
  classical
  obtain ⟨A, N₁, hA, hU⟩ := h
  obtain ⟨L, hL5, hlogL⟩ := exists_L A
  have hLr : (5 : ℝ) ≤ L := by exact_mod_cast hL5
  have hlogL0 : 0 < Real.log L := Real.log_pos (by linarith)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set δ := deltaL L with hδ
  set α := A * (3 * Real.log 4 / (L * Real.log L)) with hα
  have hδ0 : 3 / (8 * (L : ℝ)) ≤ δ := by
    refine le_trans ?_ (deltaL_ge (by omega))
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hδpos : 0 < δ := lt_of_lt_of_le (by positivity) hδ0
  have hα0 : 0 ≤ α := by positivity
  have hαδ : α ≤ δ / 2 := by
    have : α ≤ 3 / (16 * (L : ℝ)) := by
      rw [hα, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hlogL (show (0 : ℝ) ≤ 3 * L by positivity)]
    have h2 : 3 / (16 * (L : ℝ)) = (3 / (8 * (L : ℝ))) / 2 := by field_simp; ring
    linarith
  set ε := δ / 4 with hε
  have hεpos : 0 < ε := by positivity
  -- the upper bound for `θ_{T_L}`
  have hθT : ∀ᶠ N : ℕ in atTop, thetaS (TL L) N ≤ (α + ε) * N := by
    filter_upwards [eventually_ge_atTop ⌈N₁⌉₊, eventually_ge_atTop 2,
      eventually_rpow_mul_log_le hεpos] with N hN1 hN2 hlog
    have hN1' : N₁ ≤ N := (Nat.ceil_le.1 hN1)
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
    have hc := card_TL_le hA hU hL5 hN1' hN2
    calc thetaS (TL L) N
        ≤ Real.log N * (((range (N + 1)).filter (· ∈ TL L)).card : ℝ) :=
          thetaS_le_log_mul_card _ N
      _ ≤ Real.log N * (α * N / Real.log N + 20 * (N : ℝ) ^ ((3 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hc hlogN.le
      _ = α * N + 20 * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log N := by field_simp
      _ ≤ (α + ε) * N := by nlinarith
  obtain ⟨B, hB⟩ := thetaS_le_of_eventually (by positivity) hθT
  -- the main term
  obtain ⟨K, hK⟩ := phi_CL_lower L
  refine primesRelUpperDensityPos_of_dirichlet (η := δ - α - ε) (K := K + B + α + ε)
    (by linarith) fun x hx => ?_
  have hx1 : 1 < x := hx.1
  have hx2 : x ≤ 2 := hx.2
  have hx0 : 0 < x - 1 := by linarith
  have hCx := hK x hx
  have hTx := (abel_bound (by positivity) hB hx1 hx2).2
  -- `Φ_G ≥ Φ_{C_L} − Φ_{T_L}`
  have hsG := summable_phiTerm goodSlopePrimes_subset_primes hx1 hx2
  have hsC := summable_phiTerm (CL_subset_primes L) hx1 hx2
  have hsT := summable_phiTerm (TL_subset_primes L) hx1 hx2
  have hterm : ∀ n : ℕ, phiTerm (CL L) x n - phiTerm (TL L) x n ≤
      phiTerm {p | GoodSlopePrime p} x n := by
    intro n
    have hT0 := phiTerm_nonneg (TL L) x n
    have hG0 := phiTerm_nonneg {p | GoodSlopePrime p} x n
    by_cases hnC : n ∈ CL L
    · by_cases hnT : n ∈ TL L
      · have : phiTerm (CL L) x n = phiTerm (TL L) x n := by
          simp only [phiTerm, Set.indicator_of_mem hnC, Set.indicator_of_mem hnT]
        linarith
      · have hnG : n ∈ {p | GoodSlopePrime p} := goodSlopePrime_of_mem_CL hnC hnT
        have : phiTerm (CL L) x n = phiTerm {p | GoodSlopePrime p} x n := by
          simp only [phiTerm, Set.indicator_of_mem hnC, Set.indicator_of_mem hnG]
        linarith
    · have : phiTerm (CL L) x n = 0 := by simp [phiTerm, Set.indicator_of_notMem hnC]
      linarith
  have hGlow : PhiS (CL L) x - PhiS (TL L) x ≤ PhiS {p | GoodSlopePrime p} x := by
    rw [PhiS, PhiS, PhiS, ← Summable.tsum_sub hsC hsT]
    exact Summable.tsum_le_tsum hterm (hsC.sub hsT) hsG
  have hxx : x / (x - 1) = 1 + 1 / (x - 1) := by field_simp; ring
  rw [hxx] at hTx
  have e1 : (δ - α - ε) / (x - 1) = δ / (x - 1) - (α + ε) * (1 / (x - 1)) := by ring
  rw [e1]
  nlinarith

/-- **22P_AP from Green–Tao and the uniform bad-prime bound.** -/
theorem goodPrimeAP_of_greenTaoDense_uniformBadBound (hGT : GreenTaoDense)
    (hU : UniformBadBound) : GoodPrimeAP :=
  goodPrimeAP_of_greenTaoDense hGT (goodPrimeDensity_of_uniformBadBound hU)

end ZInQ.Density
