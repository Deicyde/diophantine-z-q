import ZInQKernel.Progressions.LSeries.Tail

/-!
# Bounds for `L(σ, χ)` and `L'(σ, χ)` near `σ = 1`

Plan step 1, `docs/effective-dirichlet-plan.md`. For `χ ≠ 1` mod `q` and `M = log q + 3`:

* `norm_LFunction_le`: `‖L(σ,χ)‖ ≤ M` for real `σ ≥ 1`;
* `norm_deriv_LFunction_le`: `‖L'(σ,χ)‖ ≤ M²` for real `σ > 1`;
* `norm_LFunction_sub_one_le`: `‖L(σ,χ) − L(1,χ)‖ ≤ (σ − 1) M²` for real `σ ≥ 1`;
* `norm_LFunction_one_le`: `‖L(1,χ)‖ ≤ M`.

The plan states these for `σ ∈ (1, 2]`; they hold for every `σ > 1` (resp. `σ ≥ 1`).
-/

open Finset Complex

namespace ZInQ.Progressions

variable {q : ℕ} [NeZero q]

/-- A nontrivial character has modulus at least 2. -/
theorem two_le_modulus_of_char_ne_one {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) : 2 ≤ q := by
  by_contra h
  have hq : q = 1 := by have := NeZero.ne q; omega
  exact hχ (DirichletCharacter.level_one' χ hq)

omit [NeZero q] in
/-- `∑_{0 < n ≤ N} 1/n ≤ 1 + log N`, in the spelling used here. -/
theorem sum_Ioc_natCast_inv_le_one_add_log (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ((n : ℝ))⁻¹ ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have e : Finset.Ioc 0 N = Finset.Icc 1 N := by ext n; simp; omega
  rwa [e]

omit [NeZero q] in
/-- Head of the L-series: `∑_{0 < n ≤ N} ‖χ(n)/n^σ‖ ≤ 1 + log N` for `σ ≥ 1`. -/
theorem sum_norm_char_div_cpow_le (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 ≤ σ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ‖χ n / (n : ℂ) ^ (σ : ℂ)‖ ≤ 1 + Real.log N := by
  refine le_trans (Finset.sum_le_sum fun n hn ↦ ?_) (sum_Ioc_natCast_inv_le_one_add_log N)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
  rw [char_div_cpow_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), ← Real.rpow_neg_one]
  calc ‖χ n‖ * (n : ℝ) ^ (-σ) ≤ 1 * (n : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right (χ.norm_le_one n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ (n : ℝ) ^ (-1 : ℝ) := by
        rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)

omit [NeZero q] in
/-- Head of the logarithmic L-series:
`∑_{0 < n ≤ N} ‖χ(n) log n/n^σ‖ ≤ log N (1 + log N)` for `σ ≥ 1`. -/
theorem sum_norm_char_log_div_cpow_le (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 ≤ σ)
    (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ‖χ n * (Real.log n : ℂ) / (n : ℂ) ^ (σ : ℂ)‖ ≤
      Real.log N * (1 + Real.log N) := by
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  refine le_trans (Finset.sum_le_sum fun n hn ↦ ?_)
    ((Finset.mul_sum _ _ _).symm.le.trans
      (mul_le_mul_of_nonneg_left (sum_Ioc_natCast_inv_le_one_add_log N) hlogN))
  have hn := Finset.mem_Ioc.mp hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2
  rw [char_log_div_cpow_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.log_natCast_nonneg n)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)), ← Real.rpow_neg_one]
  have h1 : (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h2 : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hnN
  have h3 : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h4 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  calc ‖χ n‖ * (Real.log n * (n : ℝ) ^ (-σ)) ≤ 1 * (Real.log n * (n : ℝ) ^ (-σ)) :=
        mul_le_mul_of_nonneg_right (χ.norm_le_one n) (mul_nonneg h4 h3)
    _ ≤ Real.log N * (n : ℝ) ^ (-1 : ℝ) := by
        rw [one_mul]; exact mul_le_mul h2 h1 h3 hlogN

/-- `‖L(σ,χ)‖ ≤ log q + 3` for real `σ > 1`. -/
theorem norm_LFunction_le_of_one_lt {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 1 < σ) : ‖DirichletCharacter.LFunction χ σ‖ ≤ Real.log q + 3 := by
  set P := ∑ n ∈ Ioc 0 q, χ n / (n : ℂ) ^ (σ : ℂ)
  have htail := norm_LFunction_sub_sum_le hχ hσ q
  have hhead : ‖P‖ ≤ 1 + Real.log q :=
    (norm_sum_le _ _).trans (sum_norm_char_div_cpow_le χ hσ.le q)
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : (q : ℝ) * ((q + 1 : ℕ) : ℝ) ^ (-σ) ≤ 1 := by
    refine (mul_le_mul_of_nonneg_left (natSucc_rpow_neg_le_inv hσ.le q) hq).trans ?_
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    push_cast; linarith
  calc ‖DirichletCharacter.LFunction χ σ‖
      ≤ ‖DirichletCharacter.LFunction χ σ - P‖ + ‖P‖ := norm_le_norm_sub_add _ _
    _ ≤ 1 + (1 + Real.log q) := add_le_add (htail.trans h1) hhead
    _ ≤ Real.log q + 3 := by linarith

/-- The real-variable restriction `t ↦ L(t,χ)` is continuous for `χ ≠ 1`. -/
theorem continuous_LFunction_ofReal {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Continuous fun t : ℝ ↦ DirichletCharacter.LFunction χ t :=
  (DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal

/-- A closed bound on `L(σ,χ)` for `σ > 1` passes to `σ = 1` by continuity. -/
theorem LFunction_one_le_of_forall_one_lt {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {g : ℂ → ℝ}
    (hg : Continuous g) {C : ℝ}
    (h : ∀ σ : ℝ, 1 < σ → g (DirichletCharacter.LFunction χ σ) ≤ C) :
    g (DirichletCharacter.LFunction χ 1) ≤ C := by
  have hc : ContinuousAt (fun t : ℝ ↦ g (DirichletCharacter.LFunction χ t)) 1 :=
    (hg.comp (continuous_LFunction_ofReal hχ)).continuousAt
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
  simp only [Complex.ofReal_one] at ht
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun σ hσ ↦ h σ hσ)

/-- Plan step 1: `‖L(σ,χ)‖ ≤ M = log q + 3` for real `σ ≥ 1`. -/
theorem norm_LFunction_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ : ℝ} (hσ : 1 ≤ σ) :
    ‖DirichletCharacter.LFunction χ σ‖ ≤ Real.log q + 3 := by
  rcases hσ.lt_or_eq with hσ | rfl
  · exact norm_LFunction_le_of_one_lt hχ hσ
  · rw [Complex.ofReal_one]
    exact LFunction_one_le_of_forall_one_lt hχ continuous_norm fun σ hσ ↦ norm_LFunction_le_of_one_lt hχ hσ

/-- Plan step 1: `‖L(1,χ)‖ ≤ M`. -/
theorem norm_LFunction_one_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤ Real.log q + 3 := by
  simpa using norm_LFunction_le hχ le_rfl

/-- For `σ > 1`, `L'(σ,χ) = -∑ χ(n) log n / n^σ`. -/
theorem deriv_LFunction_eq (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    deriv (DirichletCharacter.LFunction χ) σ =
      -LSeries (LSeries.logMul (fun n ↦ χ n)) σ := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds (σ : ℂ)] LSeries (fun n ↦ χ n) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with s hs' using χ.LFunction_eq_LSeries hs'
  rw [hev.deriv_eq]
  refine LSeries_deriv ?_
  simp only [Complex.ofReal_re]
  exact (abscissaOfAbsConv_char_le_one χ).trans_lt (by exact_mod_cast hσ)

omit [NeZero q] in
/-- `q log(q+1) (q+1)^(-σ) ≤ log q + 1` for `q ≥ 2`, `σ ≥ 1`. -/
theorem mul_log_succ_rpow_neg_le {σ : ℝ} (hσ : 1 ≤ σ) (hq2 : 2 ≤ q) :
    (q : ℝ) * (Real.log ((q + 1 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ) ^ (-σ)) ≤ Real.log q + 1 := by
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq1 : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  have hl : 0 ≤ Real.log ((q + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  calc (q : ℝ) * (Real.log ((q + 1 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ) ^ (-σ))
      ≤ q * (Real.log ((q + 1 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (natSucc_rpow_neg_le_inv hσ q) hl) (by positivity)
    _ ≤ Real.log ((q + 1 : ℕ) : ℝ) := by
        rw [← mul_assoc, mul_comm (q : ℝ), mul_assoc]
        refine mul_le_of_le_one_right hl ?_
        rw [← div_eq_mul_inv, div_le_one hq1]; push_cast; linarith
    _ ≤ Real.log (2 * q) := Real.log_le_log hq1 (by push_cast; linarith)
    _ = Real.log 2 + Real.log q := Real.log_mul (by norm_num) (by linarith)
    _ ≤ Real.log q + 1 := by linarith [Real.log_two_lt_d9]

/-- Plan step 1: `‖L'(σ,χ)‖ ≤ M²` for real `σ > 1`. -/
theorem norm_deriv_LFunction_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 1 < σ) : ‖deriv (DirichletCharacter.LFunction χ) σ‖ ≤ (Real.log q + 3) ^ 2 := by
  rw [deriv_LFunction_eq χ hσ, norm_neg]
  have hq2 := two_le_modulus_of_char_ne_one hχ
  set P := ∑ n ∈ Ioc 0 q, χ n * (Real.log n : ℂ) / (n : ℂ) ^ (σ : ℂ)
  have htail := norm_LSeries_logMul_sub_sum_le hχ hσ hq2
  have hhead : ‖P‖ ≤ Real.log q * (1 + Real.log q) :=
    (norm_sum_le _ _).trans (sum_norm_char_log_div_cpow_le χ hσ.le q)
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have h1 := mul_log_succ_rpow_neg_le hσ.le hq2
  calc ‖LSeries (LSeries.logMul (fun n ↦ χ n)) σ‖
      ≤ ‖LSeries (LSeries.logMul (fun n ↦ χ n)) σ - P‖ + ‖P‖ := norm_le_norm_sub_add _ _
    _ ≤ (Real.log q + 1) + Real.log q * (1 + Real.log q) := add_le_add (htail.trans h1) hhead
    _ ≤ (Real.log q + 3) ^ 2 := by nlinarith

/-- Plan step 1: `‖L(σ,χ) − L(1,χ)‖ ≤ (σ − 1) M²` for real `σ ≥ 1` (mean value inequality). -/
theorem norm_LFunction_sub_one_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 1 ≤ σ) :
    ‖DirichletCharacter.LFunction χ σ - DirichletCharacter.LFunction χ 1‖ ≤
      (σ - 1) * (Real.log q + 3) ^ 2 := by
  set L := DirichletCharacter.LFunction χ
  -- Reflect `[1, σ]` so that the excluded endpoint of the bound is `t = 1`.
  set h : ℝ → ℂ := fun t ↦ L ((σ + 1 - t : ℝ) : ℂ)
  have hd : ∀ t, HasDerivAt h (-deriv L ((σ + 1 - t : ℝ) : ℂ)) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ ↦ L u) (deriv L ((σ + 1 - t : ℝ) : ℂ)) (σ + 1 - t) :=
      ((DirichletCharacter.differentiable_LFunction hχ) _).hasDerivAt.comp_ofReal
    have h2 : HasDerivAt (fun t : ℝ ↦ σ + 1 - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (σ + 1)
    have := h1.scomp t h2
    simpa [h, Function.comp_def] using this
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := h) (a := 1) (b := σ)
    (C := (Real.log q + 3) ^ 2) (fun t _ ↦ (hd t).hasDerivWithinAt) (fun t ht ↦ by
      rw [norm_neg]
      exact norm_deriv_LFunction_le hχ (by linarith [ht.1, ht.2]))
    σ (Set.right_mem_Icc.mpr hσ)
  have e1 : h σ = L 1 := by simp [h]
  have e2 : h 1 = L σ := by simp [h]
  rw [e1, e2, norm_sub_rev] at key
  linarith

end ZInQ.Progressions
