import Mathlib

/-! # cm-branch: the arithmetic of the manuscript's CM paragraph (diophantine_zq.tex L581-631)

Pure Mathlib. Formalizes:
* the expansion of the summand of [cmheight, Eq. (6.2)] (`summand62_eq_archSummand`, L601-604);
* the q-series estimate `−2 Σ log|1 − qⁿ| ≤ 2ρ/(1−ρ)² < 200/9801` and `−½ log y < 1/10` (L605-607);
* the summand bound `≤ π y/6 + 1` (L607-611) and `π√|Δ|/12 + 1 ≤ D² 3^{21000 D²} + 1 = B_cm` (L611-612).
-/

open Real Complex
open scoped UpperHalfPlane

namespace CMBranch

/-- The modular discriminant in the normalization of [cmheight, Eq. (6.2)]: `Δ(τ) = (2π)¹² η(τ)²⁴`
(Mathlib's Dedekind `η`). -/
noncomputable def discAn (τ : ℂ) : ℂ := ((2 * π : ℝ) : ℂ) ^ 12 * ModularForm.eta τ ^ 24

/-- The archimedean summand of [cmheight, Eq. (6.2)]: `−(1/12) log(|Δ(τ)| (Im τ)⁶)`. -/
noncomputable def summand62 (τ : ℂ) : ℝ := -(1 / 12) * Real.log (‖discAn τ‖ * τ.im ^ 6)

/-- The same summand as expanded in the manuscript (L601-604):
`−log(2π) + π y/6 − ½ log y − 2 Σ_{n≥1} log|1 − e^{2πinτ}|`. -/
noncomputable def archSummand (τ : ℂ) : ℝ :=
  -Real.log (2 * π) + π * τ.im / 6 - (1 / 2) * Real.log τ.im -
    2 * ∑' n : ℕ, Real.log ‖1 - Complex.exp (2 * π * I * (n + 1) * τ)‖

section Expansion

variable {τ : ℂ}

lemma norm_eta_q (n : ℕ) (τ : ℂ) :
    ‖ModularForm.eta_q n τ‖ = Real.exp (-2 * π * τ.im) ^ (n + 1) := by
  rw [ModularForm.eta_q_eq_cexp, Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  push_cast
  ring

lemma rho_lt_one (hτ : 0 < τ.im) : Real.exp (-2 * π * τ.im) < 1 := by
  rw [Real.exp_lt_one]
  have := Real.pi_pos
  nlinarith

lemma summable_norm_eta_q (hτ : 0 < τ.im) : Summable fun n => ‖ModularForm.eta_q n τ‖ := by
  simp_rw [norm_eta_q]
  have h0 : 0 ≤ Real.exp (-2 * π * τ.im) := (Real.exp_pos _).le
  exact (summable_geometric_of_lt_one h0 (rho_lt_one hτ)).comp_injective
    (fun a b h => by simpa using h)

/-- `w n = log(1 − qₙ)` (complex logarithm) is summable. -/
lemma summable_clog (hτ : 0 < τ.im) :
    Summable fun n => Complex.log (1 + -ModularForm.eta_q n τ) := by
  apply Complex.summable_log_one_add_of_summable
  exact (summable_norm_eta_q hτ).of_norm.neg

lemma summable_log_norm (hτ : 0 < τ.im) :
    Summable fun n : ℕ => Real.log ‖1 - ModularForm.eta_q n τ‖ := by
  have h := (summable_clog hτ).mapL Complex.reCLM
  refine h.congr fun n => ?_
  simp [Complex.log_re, sub_eq_add_neg]

lemma norm_tprod_eq (hτ : 0 < τ.im) :
    ‖∏' n, (1 - ModularForm.eta_q n τ)‖ =
      Real.exp (∑' n : ℕ, Real.log ‖1 - ModularForm.eta_q n τ‖) := by
  have hne : ∀ n, (1 + -ModularForm.eta_q n τ) ≠ 0 := fun n => by
    rw [← sub_eq_add_neg]; exact ModularForm.one_sub_eta_q_ne_zero n hτ
  have hprod := Complex.cexp_tsum_eq_tprod hne (summable_clog hτ)
  simp_rw [← sub_eq_add_neg] at hprod
  rw [← hprod, Complex.norm_exp]
  congr 1
  rw [Complex.re_tsum (by simpa [sub_eq_add_neg] using summable_clog hτ)]
  simp [Complex.log_re]

lemma norm_qParam24 (τ : ℂ) :
    ‖Function.Periodic.qParam 24 τ‖ = Real.exp (-2 * π * τ.im / 24) := by
  rw [Function.Periodic.norm_qParam]
  ring_nf

/-- **The expansion of Eq. (6.2)'s summand** (manuscript L601-604). -/
theorem summand62_eq_archSummand (hτ : 0 < τ.im) : summand62 τ = archSummand τ := by
  set S := ∑' n : ℕ, Real.log ‖1 - ModularForm.eta_q n τ‖ with hS
  have hη : ‖ModularForm.eta τ‖ = Real.exp (-2 * π * τ.im / 24) * Real.exp S := by
    rw [ModularForm.eta, norm_mul, norm_qParam24, norm_tprod_eq hτ]
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hD : ‖discAn τ‖ = (2 * π) ^ 12 * (Real.exp (-2 * π * τ.im) * Real.exp (24 * S)) := by
    rw [discAn, norm_mul, norm_pow, norm_pow, hη, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos h2π, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 2 <;> push_cast <;> ring
  have hS' : S = ∑' n : ℕ, Real.log ‖1 - Complex.exp (2 * π * I * (n + 1) * τ)‖ := by
    rw [hS]; simp_rw [ModularForm.eta_q_eq_cexp]
  rw [summand62, archSummand, hD, ← hS', Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_exp, Real.log_exp]
  push_cast
  ring

end Expansion

section Bounds

/-- `−log(1 − a) ≤ a/(1 − a)` for `0 ≤ a < 1`. -/
lemma neg_log_one_sub_le {a : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) :
    -Real.log (1 - a) ≤ a / (1 - a) := by
  have hpos : 0 < 1 - a := by linarith
  have := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at this
  calc -Real.log (1 - a) ≤ (1 - a)⁻¹ - 1 := this
    _ = a / (1 - a) := by field_simp; ring

/-- **The q-series estimate** (manuscript L605-606): for `y = Im τ > 0` and `ρ = e^{−2πy}`,
`−Σ_{n≥1} log|1 − qⁿ| ≤ ρ/(1 − ρ)²`. -/
theorem neg_tsum_log_le {τ : ℂ} (hτ : 0 < τ.im) :
    -(∑' n : ℕ, Real.log ‖1 - Complex.exp (2 * π * I * (n + 1) * τ)‖) ≤
      Real.exp (-2 * π * τ.im) / (1 - Real.exp (-2 * π * τ.im)) ^ 2 := by
  set ρ := Real.exp (-2 * π * τ.im) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := rho_lt_one hτ
  have h1ρ : 0 < 1 - ρ := by linarith
  simp_rw [← ModularForm.eta_q_eq_cexp]
  have hsum := summable_log_norm hτ
  have hg : Summable fun n : ℕ => ρ ^ (n + 1) / (1 - ρ) :=
    ((summable_geometric_of_lt_one hρ0 hρ1).comp_injective
      (fun a b h => by simpa using h)).div_const _
  have hpt : ∀ n : ℕ, -Real.log ‖1 - ModularForm.eta_q n τ‖ ≤ ρ ^ (n + 1) / (1 - ρ) := by
    intro n
    have hq : ‖ModularForm.eta_q n τ‖ = ρ ^ (n + 1) := norm_eta_q n τ
    have ha0 : 0 ≤ ρ ^ (n + 1) := pow_nonneg hρ0 _
    have haρ : ρ ^ (n + 1) ≤ ρ := pow_le_of_le_one hρ0 hρ1.le (Nat.succ_ne_zero n)
    have ha1 : ρ ^ (n + 1) < 1 := lt_of_le_of_lt haρ hρ1
    have hlow : 1 - ρ ^ (n + 1) ≤ ‖1 - ModularForm.eta_q n τ‖ := by
      have := norm_sub_norm_le (1 : ℂ) (ModularForm.eta_q n τ)
      rw [norm_one, hq] at this; exact this
    have hpos : 0 < 1 - ρ ^ (n + 1) := by linarith
    calc -Real.log ‖1 - ModularForm.eta_q n τ‖ ≤ -Real.log (1 - ρ ^ (n + 1)) := by
          have := Real.log_le_log hpos hlow; linarith
      _ ≤ ρ ^ (n + 1) / (1 - ρ ^ (n + 1)) := neg_log_one_sub_le ha0 ha1
      _ ≤ ρ ^ (n + 1) / (1 - ρ) := by
          apply div_le_div_of_nonneg_left ha0 h1ρ; linarith
  have htg : ∑' n : ℕ, ρ ^ (n + 1) / (1 - ρ) = ρ / (1 - ρ) ^ 2 := by
    rw [tsum_div_const]
    have : ∑' n : ℕ, ρ ^ (n + 1) = ρ / (1 - ρ) := by
      simp_rw [pow_succ]
      rw [tsum_mul_right, tsum_geometric_of_lt_one hρ0 hρ1]
      field_simp
    rw [this]; field_simp
  rw [← tsum_neg, ← htg]
  exact hsum.neg.tsum_le_tsum hpt hg

lemma exp_five_gt : (100 : ℝ) < Real.exp 5 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h0 : (0 : ℝ) ≤ 2.7182818283 := by norm_num
  calc (100 : ℝ) < 2.7182818283 ^ 5 := by norm_num
    _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ h0 h.le 5

lemma sqrt3_gt : (1.73 : ℝ) < Real.sqrt 3 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

/-- `ρ = e^{−2πy} < 1/100` for `y ≥ √3/2` (manuscript L605). -/
lemma rho_lt_hundredth {y : ℝ} (hy : Real.sqrt 3 / 2 ≤ y) :
    Real.exp (-2 * π * y) < 1 / 100 := by
  have hpi := Real.pi_gt_three
  have h3 := sqrt3_gt
  have h5 : 5 ≤ 2 * π * y := by nlinarith
  have : Real.exp (-2 * π * y) ≤ Real.exp (-5) := Real.exp_le_exp.mpr (by linarith)
  have h := exp_five_gt
  rw [Real.exp_neg] at this
  calc Real.exp (-2 * π * y) ≤ (Real.exp 5)⁻¹ := this
    _ < 1 / 100 := by rw [one_div]; exact inv_strictAnti₀ (by norm_num) h

/-- **The summand bound** (manuscript L605-611): for a period `τ` with `√3/2 ≤ Im τ`,
`archSummand τ ≤ π (Im τ)/6 + 1`. (The manuscript discards `−log 2π < 0`, bounds the sum by
`2ρ/(1−ρ)² < 200/9801` and `−½ log y < 1/10`, and enlarges their sum to `1`.) -/
theorem archSummand_le {τ : ℂ} (hy : Real.sqrt 3 / 2 ≤ τ.im) :
    archSummand τ ≤ π * τ.im / 6 + 1 := by
  have h3 := sqrt3_gt
  have hy0 : 0 < τ.im := by linarith
  set ρ := Real.exp (-2 * π * τ.im) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρs : ρ < 1 / 100 := rho_lt_hundredth hy
  have hq := neg_tsum_log_le hy0
  rw [← hρ] at hq
  have hq' : ρ / (1 - ρ) ^ 2 ≤ (1 / 100) / (99 / 100) ^ 2 := by
    apply div_le_div₀ (by norm_num) hρs.le (by norm_num)
    nlinarith
  have hlog2pi : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogy : -(1 / 2) * Real.log τ.im ≤ 1 / 10 := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hy0)
    rw [Real.log_inv] at this
    have hinv : τ.im⁻¹ ≤ 1 / 0.865 := by
      rw [inv_le_comm₀ hy0 (by norm_num)]; norm_num; linarith
    linarith
  unfold archSummand
  linarith

/-- **`π√|Δ|/12 + 1 ≤ B_cm`** from Fowler's bound (manuscript L611-612), over variables:
if `0 ≤ s ≤ 2D² exp(21000 D²)` then `π s/12 + 1 ≤ D² 3^{21000 D²} + 1`. -/
theorem bcm_of_fowler (D : ℕ) {s : ℝ} (hs : s ≤ 2 * (D : ℝ) ^ 2 * Real.exp (21000 * (D : ℝ) ^ 2)) :
    π * s / 12 + 1 ≤ (D : ℝ) ^ 2 * 3 ^ (21000 * D ^ 2) + 1 := by
  have hpi := Real.pi_lt_four
  have hpi0 := Real.pi_pos
  have hexp : Real.exp (21000 * (D : ℝ) ^ 2) ≤ (3 : ℝ) ^ (21000 * D ^ 2) := by
    have : Real.exp (21000 * (D : ℝ) ^ 2) = Real.exp 1 ^ (21000 * D ^ 2) := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [this]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) _
  have hD2 : (0 : ℝ) ≤ (D : ℝ) ^ 2 := by positivity
  have hE0 : 0 ≤ Real.exp (21000 * (D : ℝ) ^ 2) := (Real.exp_pos _).le
  have h1 : π * s / 12 ≤ π * (2 * (D : ℝ) ^ 2 * Real.exp (21000 * (D : ℝ) ^ 2)) / 12 := by
    have := mul_le_mul_of_nonneg_left hs hpi0.le; linarith
  have h2 : π * (2 * (D : ℝ) ^ 2 * Real.exp (21000 * (D : ℝ) ^ 2)) / 12 ≤
      (D : ℝ) ^ 2 * Real.exp (21000 * (D : ℝ) ^ 2) := by
    have : 0 ≤ (D : ℝ) ^ 2 * Real.exp (21000 * (D : ℝ) ^ 2) := mul_nonneg hD2 hE0
    nlinarith
  have h3 : (D : ℝ) ^ 2 * Real.exp (21000 * (D : ℝ) ^ 2) ≤ (D : ℝ) ^ 2 * 3 ^ (21000 * D ^ 2) :=
    mul_le_mul_of_nonneg_left hexp hD2
  linarith

end Bounds

end CMBranch
