import ZInQKernel.Density.Abel

/-!
# The prime tail `Σ_{ℓ > L} ℓ^{−2}` (pd-paper Lemma 5.1)

`sum_inv_sq_le_of_primes_gt`: for `L ≥ 2` and every finite set `F` of primes `> L`,
`Σ_{ℓ ∈ F} ℓ^{−2} ≤ 3 log 4 / (L log L)`, which is stronger than the note's `4 log 4/(L log L)`
(`prime_tail`). Proof: `ℓ^{−2} ≤ (log ℓ/log L) ℓ^{−2}`, then Abel summation against
Chebyshev's bound `θ(m) ≤ m log 4` (instead of the note's dyadic decomposition).
-/

namespace ZInQ.Density

open Finset

theorem mul_inv_sq_sub_le (m : ℝ) (hm : 0 < m) :
    m * (1 / m ^ 2 - 1 / (m + 1) ^ 2) ≤ 2 * (1 / m - 1 / (m + 1)) := by
  have h1 : 0 < m + 1 := by linarith
  have e1 : m * (1 / m ^ 2 - 1 / (m + 1) ^ 2) = (2 * m + 1) / (m * (m + 1) ^ 2) := by
    field_simp; ring
  have e2 : 2 * (1 / m - 1 / (m + 1)) = 2 / (m * (m + 1)) := by
    field_simp; ring
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos hm 2, pow_pos hm 3, mul_pos hm h1]

/-- Telescoping: `Σ_{L < m < M} (1/m − 1/(m + 1)) = 1/(L + 1) − 1/max(M, L + 1)`. -/
theorem sum_tel_gt (L M : ℕ) :
    ∑ m ∈ range M, (if L < m then (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) else 0) =
      1 / ((L : ℝ) + 1) - 1 / (max M (L + 1) : ℕ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih]
    by_cases h : L < M
    · simp only [h, ↓reduceIte]; rw [max_eq_left (by omega), max_eq_left (by omega)]
      push_cast; ring
    · simp only [h, ↓reduceIte]; rw [max_eq_right (by omega), max_eq_right (by omega)]
      ring

/-- Abel summation against Chebyshev: `Σ_{L < p ≤ M, p prime} log p / p² ≤ 3 log 4 / L`. -/
theorem sum_log_div_sq_le {L : ℕ} (hL : 1 ≤ L) (M : ℕ) :
    ∑ n ∈ range (M + 1), {n : ℕ | n.Prime ∧ L < n}.indicator (fun n : ℕ => Real.log n) n *
      (1 / (n : ℝ) ^ 2) ≤ 3 * Real.log 4 / L := by
  set S : Set ℕ := {n : ℕ | n.Prime ∧ L < n} with hS
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hA : ∀ m : ℕ, thetaS S m ≤ Real.log 4 * m := fun m => by
    simpa using thetaS_le_log4 (S := S) (fun n hn => hn.1) m
  have hA0 : ∀ m : ℕ, m ≤ L → thetaS S m = 0 := by
    intro m hm
    refine sum_eq_zero fun n hn => Set.indicator_of_notMem ?_ _
    intro h
    have := mem_range.1 hn
    exact absurd h.2 (by omega)
  rw [abel_summation]
  -- each Abel term
  have hterm : ∀ m : ℕ, (∑ n ∈ range (m + 1), S.indicator (fun n : ℕ => Real.log n) n) *
      (1 / (m : ℝ) ^ 2 - 1 / ((m + 1 : ℕ) : ℝ) ^ 2) ≤
      2 * Real.log 4 * (if L < m then (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) else 0) := by
    intro m
    change thetaS S m * _ ≤ _
    by_cases h : L < m
    · simp only [h, ↓reduceIte]
      have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hd : 0 ≤ 1 / (m : ℝ) ^ 2 - 1 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
        rw [sub_nonneg]; push_cast
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
      calc thetaS S m * (1 / (m : ℝ) ^ 2 - 1 / ((m + 1 : ℕ) : ℝ) ^ 2)
          ≤ Real.log 4 * m * (1 / (m : ℝ) ^ 2 - 1 / ((m + 1 : ℕ) : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right (hA m) hd
        _ = Real.log 4 * (m * (1 / (m : ℝ) ^ 2 - 1 / ((m : ℝ) + 1) ^ 2)) := by push_cast; ring
        _ ≤ Real.log 4 * (2 * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left (mul_inv_sq_sub_le m hm) hl4.le
        _ = _ := by ring
    · simp only [h, ↓reduceIte]; rw [hA0 m (by omega)]; simp
  have hlast : (∑ n ∈ range (M + 1), S.indicator (fun n : ℕ => Real.log n) n) *
      (1 / (M : ℝ) ^ 2) ≤ Real.log 4 / L := by
    change thetaS S M * _ ≤ _
    by_cases h : L < M
    · have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      have hLM : (L : ℝ) ≤ M := by exact_mod_cast h.le
      calc thetaS S M * (1 / (M : ℝ) ^ 2) ≤ Real.log 4 * M * (1 / (M : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right (hA M) (by positivity)
        _ = Real.log 4 / M := by field_simp
        _ ≤ Real.log 4 / L := div_le_div_of_nonneg_left hl4.le (by linarith) hLM
    · rw [hA0 M (by omega), zero_mul]; positivity
  have htel := sum_tel_gt L M
  have hmax : 0 ≤ 1 / ((max M (L + 1) : ℕ) : ℝ) := by positivity
  have hL1 : 1 / ((L : ℝ) + 1) ≤ 1 / L := one_div_le_one_div_of_le (by linarith) (by linarith)
  calc _ ≤ ∑ m ∈ range M, 2 * Real.log 4 *
          (if L < m then (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) else 0) + Real.log 4 / L :=
        add_le_add (sum_le_sum fun m _ => hterm m) hlast
    _ = 2 * Real.log 4 * (1 / ((L : ℝ) + 1) - 1 / ((max M (L + 1) : ℕ) : ℝ)) +
          Real.log 4 / L := by rw [← mul_sum, htel]
    _ ≤ 2 * Real.log 4 * (1 / L) + Real.log 4 / L := by gcongr; linarith
    _ = 3 * Real.log 4 / L := by ring

/-- **Lemma 5.1 (prime tail), finite form.** For `L ≥ 2` and every finite set `F` of primes
`> L`, `Σ_{ℓ ∈ F} ℓ^{−2} ≤ 3 log 4 / (L log L)`. -/
theorem sum_inv_sq_le_of_primes_gt {L : ℕ} (hL : 2 ≤ L) (F : Finset ℕ)
    (hF : ∀ ℓ ∈ F, ℓ.Prime ∧ L < ℓ) :
    ∑ ℓ ∈ F, (1 : ℝ) / (ℓ : ℝ) ^ 2 ≤ 3 * Real.log 4 / (L * Real.log L) := by
  set S : Set ℕ := {n : ℕ | n.Prime ∧ L < n} with hS
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  set M := F.sup id with hM
  have hFM : F ⊆ range (M + 1) := fun ℓ hℓ =>
    mem_range.2 (Nat.lt_succ_of_le (le_sup (f := id) hℓ))
  have key : ∀ n : ℕ, S.indicator (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) n ≤
      (1 / Real.log L) * (S.indicator (fun n : ℕ => Real.log n) n * (1 / (n : ℝ) ^ 2)) := by
    intro n
    by_cases hn : n ∈ S
    · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn]
      have hn2 : (L : ℝ) < n := by exact_mod_cast hn.2
      have hlog : Real.log L ≤ Real.log n := Real.log_le_log (by linarith) hn2.le
      have e : 1 / Real.log L * (Real.log n * (1 / (n : ℝ) ^ 2)) =
          (Real.log n / Real.log L) * (1 / (n : ℝ) ^ 2) := by ring
      rw [e]
      have : 1 ≤ Real.log n / Real.log L := (one_le_div hlogL).2 hlog
      have h0 : 0 ≤ (1 : ℝ) / (n : ℝ) ^ 2 := by positivity
      exact le_mul_of_one_le_left h0 this
    · simp [Set.indicator_of_notMem hn]
  calc ∑ ℓ ∈ F, (1 : ℝ) / (ℓ : ℝ) ^ 2
      = ∑ ℓ ∈ F, S.indicator (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) ℓ :=
        sum_congr rfl fun ℓ hℓ =>
          (Set.indicator_of_mem (show ℓ ∈ S from hF ℓ hℓ) (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)).symm
    _ ≤ ∑ n ∈ range (M + 1), S.indicator (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) n :=
        sum_le_sum_of_subset_of_nonneg hFM fun n _ _ =>
          Set.indicator_nonneg (fun n _ => by positivity) n
    _ ≤ ∑ n ∈ range (M + 1), (1 / Real.log L) *
          (S.indicator (fun n : ℕ => Real.log n) n * (1 / (n : ℝ) ^ 2)) :=
        sum_le_sum fun n _ => key n
    _ = (1 / Real.log L) * ∑ n ∈ range (M + 1),
          S.indicator (fun n : ℕ => Real.log n) n * (1 / (n : ℝ) ^ 2) := by rw [mul_sum]
    _ ≤ (1 / Real.log L) * (3 * Real.log 4 / L) :=
        mul_le_mul_of_nonneg_left (sum_log_div_sq_le (by omega) M) (by positivity)
    _ = 3 * Real.log 4 / (L * Real.log L) := by field_simp

/-- **Lemma 5.1 (prime tail)**, in the note's form: for `L ≥ 2` and every `M`,
`Σ_{L < ℓ ≤ M, ℓ prime} ℓ^{−2} ≤ 4 log 4 / (L log L)`. -/
theorem prime_tail {L : ℕ} (hL : 2 ≤ L) (M : ℕ) :
    ∑ ℓ ∈ (Ioc L M).filter Nat.Prime, (1 : ℝ) / (ℓ : ℝ) ^ 2 ≤
      4 * Real.log 4 / (L * Real.log L) := by
  refine (sum_inv_sq_le_of_primes_gt hL _ fun ℓ hℓ => ?_).trans ?_
  · simp only [mem_filter, mem_Ioc] at hℓ
    exact ⟨hℓ.2, hℓ.1.1⟩
  · have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
    have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
    have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    gcongr
    linarith

end ZInQ.Density
