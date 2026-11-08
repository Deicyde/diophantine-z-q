import ZInQKernel.Progressions.LSeries.Bounds

/-!
# Partial sums at `s = 1`

Plan step 1, `docs/effective-dirichlet-plan.md`. For `χ ≠ 1` mod `q` and `M = log q + 3`:

* `norm_partialSum_sub_LFunction_one_le`: `‖∑_{0<n≤x} χ(n)/n − L(1,χ)‖ ≤ 2q/x` for real
  `x ≥ 1` (and `≤ q/(N+1)` for the sum up to `N`, `norm_sum_div_sub_LFunction_one_le`);
* `norm_partialSum_log_le`: `‖∑_{0<n≤x} χ(n) log n/n‖ ≤ M²` for every real `x`.

`L(1,χ)` is reached as the limit `σ → 1⁺` of the absolutely convergent series (with the
uniform tail bound of `Tail.lean`), never through conditional convergence. The logarithmic
bound is a statement about finite sums only.
-/

open Finset Complex

namespace ZInQ.Progressions

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- `σ ↦ ∑_{0<n≤N} χ(n)/n^σ` is continuous in real `σ`. -/
theorem continuous_sum_char_div_cpow (χ : DirichletCharacter ℂ q) (N : ℕ) :
    Continuous fun σ : ℝ ↦ ∑ n ∈ Ioc 0 N, χ n / (n : ℂ) ^ (σ : ℂ) := by
  simp_rw [char_div_cpow_eq χ]
  refine continuous_finsetSum _ fun n hn ↦ continuous_const.mul ?_
  have hn : (n : ℝ) ≠ 0 := by
    have := (Finset.mem_Ioc.mp hn).1; exact_mod_cast (by omega : n ≠ 0)
  exact Complex.continuous_ofReal.comp
    (continuous_const.rpow continuous_neg fun _ ↦ Or.inl hn)

/-- `‖∑_{0<n≤N} χ(n)/n − L(1,χ)‖ ≤ q/(N+1)`. -/
theorem norm_sum_div_sub_LFunction_one_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, χ n / (n : ℂ) - DirichletCharacter.LFunction χ 1‖ ≤
      q * ((N + 1 : ℕ) : ℝ)⁻¹ := by
  set F : ℝ → ℝ := fun σ ↦
    ‖DirichletCharacter.LFunction χ σ - ∑ n ∈ Ioc 0 N, χ n / (n : ℂ) ^ (σ : ℂ)‖
  have hF : Continuous F :=
    ((continuous_LFunction_ofReal hχ).sub (continuous_sum_char_div_cpow χ N)).norm
  have ht := (hF.continuousAt (x := 1)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
  have h1 : F 1 = ‖∑ n ∈ Ioc 0 N, χ n / (n : ℂ) - DirichletCharacter.LFunction χ 1‖ := by
    simp only [F, Complex.ofReal_one, Complex.cpow_one]
    exact norm_sub_rev _ _
  rw [← h1]
  refine le_of_tendsto ht (eventually_nhdsWithin_of_forall fun σ hσ ↦ ?_)
  exact (norm_LFunction_sub_sum_le hχ hσ N).trans
    (mul_le_mul_of_nonneg_left (natSucc_rpow_neg_le_inv (le_of_lt hσ) N) (Nat.cast_nonneg q))

/-- Plan step 1: `‖∑_{0<n≤x} χ(n)/n − L(1,χ)‖ ≤ 2q/x` for real `x ≥ 1`. -/
theorem norm_partialSum_sub_LFunction_one_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ n / (n : ℂ) - DirichletCharacter.LFunction χ 1‖ ≤ 2 * q / x := by
  refine (norm_sum_div_sub_LFunction_one_le hχ ⌊x⌋₊).trans ?_
  have hx0 : 0 < x := by linarith
  have hlt : x < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one x
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [← div_eq_mul_inv]
  calc (q : ℝ) / ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ q / x := div_le_div_of_nonneg_left hq hx0 hlt.le
    _ ≤ 2 * q / x := div_le_div_of_nonneg_right (by linarith) hx0.le

/-- The bound `‖∑_{0<n≤x} χ(n)/n − L(1,χ)‖ ≤ 2q/x` for every real `x > 0`
(for `x < 1` the sum is empty and `‖L(1,χ)‖ ≤ log q + 3 ≤ 2q`). -/
theorem norm_partialSum_sub_LFunction_one_le' {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {x : ℝ} (hx : 0 < x) :
    ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ n / (n : ℂ) - DirichletCharacter.LFunction χ 1‖ ≤ 2 * q / x := by
  rcases le_or_gt 1 x with h1 | h1
  · exact norm_partialSum_sub_LFunction_one_le hχ h1
  · rw [Nat.floor_eq_zero.mpr h1, Finset.Ioc_self, Finset.sum_empty, zero_sub, norm_neg]
    have hq : (2 : ℝ) ≤ q := by exact_mod_cast two_le_modulus_of_char_ne_one hχ
    have hlog : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos (by linarith)
    refine (norm_LFunction_one_le hχ).trans ?_
    rw [le_div_iff₀ hx]
    nlinarith

/-- `‖∑_{0<n≤N} χ(n) log n/n‖ ≤ M²` for every `N`. -/
theorem norm_sum_log_div_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, χ n * (Real.log n : ℂ) / (n : ℂ)‖ ≤ (Real.log q + 3) ^ 2 := by
  have e : ∀ s : Finset ℕ, ∑ n ∈ s, χ n * (Real.log n : ℂ) / (n : ℂ) =
      ∑ n ∈ s, χ n * (Real.log n : ℂ) / (n : ℂ) ^ ((1 : ℝ) : ℂ) := by
    intro s; simp only [Complex.ofReal_one, Complex.cpow_one]
  have hq2 := two_le_modulus_of_char_ne_one hχ
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have head : ∀ K ≤ q, ‖∑ n ∈ Ioc 0 K, χ n * (Real.log n : ℂ) / (n : ℂ)‖ ≤
      Real.log q * (1 + Real.log q) := by
    intro K hK
    rw [e]
    refine (norm_sum_le _ _).trans ((sum_norm_char_log_div_cpow_le χ le_rfl K).trans ?_)
    have hlogK : Real.log K ≤ Real.log q := by
      rcases Nat.eq_zero_or_pos K with rfl | hK0
      · simpa using hlogq
      · exact Real.log_le_log (by exact_mod_cast hK0) (by exact_mod_cast hK)
    have hlogK0 : 0 ≤ Real.log K := Real.log_natCast_nonneg K
    nlinarith
  rcases le_or_gt N q with hN | hN
  · exact (head N hN).trans (by nlinarith)
  · rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le q) hN.le]
    refine (norm_add_le _ _).trans ?_
    have htail : ‖∑ n ∈ Ioc q N, χ n * (Real.log n : ℂ) / (n : ℂ)‖ ≤ Real.log q + 1 := by
      rw [e]
      exact (norm_sum_Ioc_char_log_div_cpow_le hχ le_rfl hq2 N).trans
        (mul_log_succ_rpow_neg_le le_rfl hq2)
    have := head q le_rfl
    nlinarith

/-- Plan step 1: `‖∑_{0<n≤x} χ(n) log n/n‖ ≤ M²` for every real `x`. -/
theorem norm_partialSum_log_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (x : ℝ) :
    ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * (Real.log n : ℂ) / (n : ℂ)‖ ≤ (Real.log q + 3) ^ 2 :=
  norm_sum_log_div_le hχ ⌊x⌋₊

end ZInQ.Progressions
