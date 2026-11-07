import ZInQKernel.Assembly.Local.SixLocalTests

/-!
# Real conditions on the pole input

Blueprint: `assembly/local-tests/pole-input-real.md`.

Let `R₀ > 1` be an integer and `C₁, …, C₆ ∈ K₀`. There is `q ∈ ℚ` with reduced denominator
coprime to `R₀` such that, with `a₀ = 1 - R₀ q²`, `R = R₀ a₀²`, `W = ∏ (1 + R Cⱼ²)` and
`Θ = Tr(W⁻¹)`: `a₀ ≠ 0`, `W ≠ 0`, `Θ ≠ 0` and `0 < R/Θ² < 1/2` (`poleInput_real`).

In each real embedding `τ`, `τ(W) ≥ 1` (`one_le_emb_poleW`), so `0 < Θ ≤ 2`; for `R` small,
`τ(W) < 2` and `Θ > 1` (`poleW_small`). The rationals `q = k/m` with `m = R₀ j + 1` and
`k` the integer nearest to `m/√R₀` make `R` arbitrarily small (`exists_q_small`).
-/

namespace ZInQ.Assembly

open ZInQ.Mult ZInQ.K0

/-- `Tr y = τ₊(y) + τ₋(y)`. -/
theorem trace_eq_emb (y : K0) :
    ((QuadraticAlgebra.trace y : ℚ) : ℝ) = embPlus y + embMinus y := by
  rw [K0.trace_eq, embPlus_apply, embMinus_apply]; push_cast; ring

theorem emb_poleW (τ : K0 →+* ℝ) (R : ℚ) (C : Fin 6 → K0) :
    τ (poleW R C) = ∏ j, (1 + (R : ℝ) * τ (C j) ^ 2) := by
  simp [poleW, map_prod]

theorem one_le_emb_poleW (τ : K0 →+* ℝ) {R : ℚ} (hR : 0 ≤ R) (C : Fin 6 → K0) :
    1 ≤ τ (poleW R C) := by
  rw [emb_poleW]
  have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR
  calc (1 : ℝ) = ∏ _j : Fin 6, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
        (fun j _ => le_add_of_nonneg_right (mul_nonneg hR' (sq_nonneg _)))

theorem emb_poleW_le (τ : K0 →+* ℝ) {R : ℚ} (hR : 0 ≤ R) (C : Fin 6 → K0) {c : ℝ}
    (hc : ∀ j, τ (C j) ^ 2 ≤ c) : τ (poleW R C) ≤ (1 + R * c) ^ 6 := by
  rw [emb_poleW]
  have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR
  calc ∏ j, (1 + (R : ℝ) * τ (C j) ^ 2) ≤ ∏ _j : Fin 6, (1 + (R : ℝ) * c) :=
        Finset.prod_le_prod₀ (fun j _ => by positivity)
          (fun j _ => by have := hc j; nlinarith)
    _ = _ := by simp

/-- The bound `c = Σⱼ (τ₊(Cⱼ)² + τ₋(Cⱼ)²)` on the squares of the embeddings of the `Cⱼ`. -/
noncomputable def embBound (C : Fin 6 → K0) : ℝ := ∑ j, (embPlus (C j) ^ 2 + embMinus (C j) ^ 2)

theorem embBound_nonneg (C : Fin 6 → K0) : 0 ≤ embBound C :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem embPlus_sq_le (C : Fin 6 → K0) (j : Fin 6) : embPlus (C j) ^ 2 ≤ embBound C :=
  le_trans (le_add_of_nonneg_right (sq_nonneg _))
    (Finset.single_le_sum (f := fun j => embPlus (C j) ^ 2 + embMinus (C j) ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ j))

theorem embMinus_sq_le (C : Fin 6 → K0) (j : Fin 6) : embMinus (C j) ^ 2 ≤ embBound C :=
  le_trans (le_add_of_nonneg_left (sq_nonneg _))
    (Finset.single_le_sum (f := fun j => embPlus (C j) ^ 2 + embMinus (C j) ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ j))

/-- The threshold `r = min(1/4, 1/(10(c + 1)))`. -/
noncomputable def smallR (C : Fin 6 → K0) : ℝ := min (1 / 4) (1 / (10 * (embBound C + 1)))

theorem smallR_pos (C : Fin 6 → K0) : 0 < smallR C := by
  have := embBound_nonneg C
  unfold smallR; apply lt_min (by norm_num); positivity

/-- For `0 < R ≤ r`: `W ≠ 0`, `Θ ≠ 0` and `0 < R/Θ² < 1/2`. -/
theorem poleW_small {R : ℚ} (hR : 0 < R) (C : Fin 6 → K0) (hRr : (R : ℝ) ≤ smallR C) :
    poleW R C ≠ 0 ∧ poleTheta R C ≠ 0 ∧ 0 < R / poleTheta R C ^ 2 ∧
      R / poleTheta R C ^ 2 < 1 / 2 := by
  have hc := embBound_nonneg C
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hR4 : (R : ℝ) ≤ 1 / 4 := hRr.trans (min_le_left _ _)
  have hRc : (R : ℝ) * embBound C ≤ 1 / 10 := by
    have h1 : (R : ℝ) ≤ 1 / (10 * (embBound C + 1)) := hRr.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hpow : (1 + (R : ℝ) * embBound C) ^ 6 < 2 := by
    have h0 : 0 ≤ (R : ℝ) * embBound C := by positivity
    calc (1 + (R : ℝ) * embBound C) ^ 6 ≤ (1 + 1 / 10) ^ 6 := by gcongr
      _ < 2 := by norm_num
  -- the two embeddings of `W` lie in `[1, 2)`
  have bounds : ∀ τ : K0 →+* ℝ, (∀ j, τ (C j) ^ 2 ≤ embBound C) →
      1 ≤ τ (poleW R C) ∧ τ (poleW R C) < 2 := fun τ hτ =>
    ⟨one_le_emb_poleW τ hR.le C, (emb_poleW_le τ hR.le C hτ).trans_lt hpow⟩
  obtain ⟨hp1, hp2⟩ := bounds embPlus (embPlus_sq_le C)
  obtain ⟨hm1, hm2⟩ := bounds embMinus (embMinus_sq_le C)
  have hW : poleW R C ≠ 0 := by
    intro h0; rw [h0, map_zero] at hp1; norm_num at hp1
  have hΘ : ((poleTheta R C : ℚ) : ℝ) = (embPlus (poleW R C))⁻¹ + (embMinus (poleW R C))⁻¹ := by
    rw [poleTheta, trace_eq_emb, map_inv₀, map_inv₀]
  have hinv : ∀ x : ℝ, 1 ≤ x → x < 2 → 1 / 2 < x⁻¹ := fun x h1 h2 => by
    rw [lt_inv_comm₀ (by norm_num) (by linarith)]; linarith
  have hΘ1 : (1 : ℝ) < poleTheta R C := by
    rw [hΘ]; linarith [hinv _ hp1 hp2, hinv _ hm1 hm2]
  have hΘ0 : poleTheta R C ≠ 0 := by
    intro h0; rw [h0, Rat.cast_zero] at hΘ1; norm_num at hΘ1
  refine ⟨hW, hΘ0, div_pos hR (by positivity), ?_⟩
  have : ((R / poleTheta R C ^ 2 : ℚ) : ℝ) < 1 / 2 := by
    push_cast
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have h2 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  exact Rat.cast_lt.mp (this.trans_eq h2.symm)

/-- Rationals `q` with denominator prime to `R₀` making `R₀ (1 - R₀ q²)²` small and nonzero. -/
theorem exists_q_small {R₀ : ℕ} (hR₀ : 1 < R₀) {r : ℝ} (hr : 0 < r) :
    ∃ q : ℚ, Nat.Coprime q.den R₀ ∧ 1 - (R₀ : ℚ) * q ^ 2 ≠ 0 ∧
      (((R₀ : ℚ) * (1 - R₀ * q ^ 2) ^ 2 : ℚ) : ℝ) < r := by
  obtain ⟨j, hj⟩ := exists_nat_gt (9 * (R₀ : ℝ) / r + 1)
  have hR0 : (1 : ℝ) < R₀ := by exact_mod_cast hR₀
  have hj1 : (1 : ℝ) ≤ j := by
    have : 0 ≤ 9 * (R₀ : ℝ) / r := by positivity
    linarith
  set m : ℕ := R₀ * j + 1 with hm
  have hm0 : (0 : ℝ) < m := by positivity
  have hmR : (R₀ : ℝ) * j ≤ m := by rw [hm]; push_cast; linarith
  set s : ℝ := 1 / Real.sqrt R₀ with hs
  have hsqrt : 0 < Real.sqrt R₀ := Real.sqrt_pos.mpr (by linarith)
  have hs0 : 0 < s := by positivity
  have hs2 : (R₀ : ℝ) * s ^ 2 = 1 := by
    rw [hs, div_pow, Real.sq_sqrt (by linarith)]; field_simp
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hsqrt]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  clear_value s
  set k : ℤ := round ((m : ℝ) * s) with hk
  set q : ℚ := (k : ℚ) / (m : ℚ) with hq
  have hqR : (q : ℝ) = (k : ℝ) / m := by rw [hq]; push_cast; rfl
  have hqs : |(q : ℝ) - s| ≤ 1 / (2 * m) := by
    have h := abs_sub_round ((m : ℝ) * s)
    rw [← hk] at h
    have : (q : ℝ) - s = -((m * s - k) / m) := by rw [hqR]; field_simp; ring
    rw [this, abs_neg, abs_div, abs_of_pos hm0, div_le_div_iff₀ hm0 (by positivity)]
    nlinarith
  have hqs' : |(q : ℝ) + s| ≤ 3 := by
    have : |(q : ℝ) - s| ≤ 1 := hqs.trans (by
      rw [div_le_one (by positivity)]; nlinarith)
    calc |(q : ℝ) + s| = |((q : ℝ) - s) + 2 * s| := by ring_nf
      _ ≤ |(q : ℝ) - s| + |2 * s| := abs_add_le _ _
      _ ≤ 1 + 2 := by rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * s)]; linarith
      _ = 3 := by norm_num
  refine ⟨q, ?_, ?_, ?_⟩
  · -- the reduced denominator divides `m`, which is prime to `R₀`
    have hden : (q.den : ℤ) ∣ (m : ℤ) := by
      have := Rat.den_dvd k m
      rwa [Rat.divInt_eq_div, Int.cast_natCast, ← hq] at this
    have hcop : Nat.Coprime m R₀ := by
      rw [hm, Nat.coprime_mul_left_add_left]; exact Nat.coprime_one_left _
    exact hcop.coprime_dvd_left (Int.natCast_dvd_natCast.mp hden)
  · intro h0
    have hmQ : (m : ℚ) ≠ 0 := by positivity
    have h1 : ((m : ℤ) ^ 2 : ℚ) = ((R₀ * k ^ 2 : ℤ) : ℚ) := by
      rw [hq] at h0; field_simp at h0; push_cast; linarith
    have h2 : (m : ℤ) ^ 2 = R₀ * k ^ 2 := by exact_mod_cast h1
    have h3 : R₀ ∣ m ^ 2 := by
      have : (R₀ : ℤ) ∣ ((m ^ 2 : ℕ) : ℤ) := ⟨k ^ 2, by push_cast; rw [h2]⟩
      exact Int.natCast_dvd_natCast.mp this
    have hcop : Nat.Coprime R₀ (m ^ 2) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, hm, Nat.coprime_mul_left_add_left]; exact Nat.coprime_one_left _
    have := hcop.eq_one_of_dvd h3
    omega
  · -- `|a₀| = R₀ |s - q| |s + q| ≤ 3 R₀/(2m) ≤ 3/(2j)`
    have ha : ((1 - (R₀ : ℚ) * q ^ 2 : ℚ) : ℝ) = R₀ * (s - q) * (s + q) := by
      push_cast; linear_combination -hs2
    have hab : |((1 - (R₀ : ℚ) * q ^ 2 : ℚ) : ℝ)| ≤ 3 / (2 * j) := by
      rw [ha, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < R₀), abs_sub_comm]
      calc (R₀ : ℝ) * |(q : ℝ) - s| * |s + q| ≤ R₀ * (1 / (2 * m)) * 3 := by
            gcongr
            · rwa [add_comm]
        _ = 3 * R₀ / (2 * m) := by ring
        _ ≤ 3 / (2 * j) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
    push_cast
    have hsq : ((1 - (R₀ : ℝ) * (q : ℝ) ^ 2)) ^ 2 ≤ (3 / (2 * j)) ^ 2 := by
      have := sq_le_sq' (abs_le.mp hab).1 (abs_le.mp hab).2
      push_cast at this; exact this
    calc (R₀ : ℝ) * (1 - R₀ * (q : ℝ) ^ 2) ^ 2 ≤ R₀ * (3 / (2 * j)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 9 * (R₀ : ℝ) / (4 * (j : ℝ) ^ 2) := by ring
      _ ≤ 9 * (R₀ : ℝ) / j := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ < r := by
          rw [div_lt_iff₀ (by positivity)]
          have := (div_lt_iff₀ hr).mp (show 9 * (R₀ : ℝ) / r < j by linarith)
          linarith

/-- **Real conditions on the pole input.** For an integer `R₀ > 1` and `C₁, …, C₆ ∈ K₀` there
is `q ∈ ℚ` with reduced denominator prime to `R₀` such that, with `a₀ = 1 - R₀ q²`,
`R = R₀ a₀²`, `W = ∏ (1 + R Cⱼ²)`, `Θ = Tr(W⁻¹)`: `a₀ ≠ 0`, `W ≠ 0`, `Θ ≠ 0` and
`0 < R/Θ² < 1/2`. -/
theorem poleInput_real (R₀ : ℕ) (hR₀ : 1 < R₀) (C : Fin 6 → K0) :
    ∃ q : ℚ, Nat.Coprime q.den R₀ ∧ 1 - (R₀ : ℚ) * q ^ 2 ≠ 0 ∧
      poleW (R₀ * (1 - R₀ * q ^ 2) ^ 2) C ≠ 0 ∧ poleTheta (R₀ * (1 - R₀ * q ^ 2) ^ 2) C ≠ 0 ∧
      0 < (R₀ * (1 - R₀ * q ^ 2) ^ 2) / poleTheta (R₀ * (1 - R₀ * q ^ 2) ^ 2) C ^ 2 ∧
      (R₀ * (1 - R₀ * q ^ 2) ^ 2) / poleTheta (R₀ * (1 - R₀ * q ^ 2) ^ 2) C ^ 2 < 1 / 2 := by
  obtain ⟨q, hcop, ha0, hsmall⟩ := exists_q_small hR₀ (smallR_pos C)
  have hR : 0 < (R₀ : ℚ) * (1 - R₀ * q ^ 2) ^ 2 := by
    have : (0 : ℚ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
    positivity
  exact ⟨q, hcop, ha0, poleW_small hR C hsmall.le⟩

end ZInQ.Assembly
