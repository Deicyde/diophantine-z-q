import ZInQKernel.Contrib.CloudB3SC7T21.LBounds

/-!
# t21-proof: `0 < ‖𝓛(m)²‖ < 4` at `m = 1, 3`

Task t21-proof. `0.09 < Re L(C_1, 1)`, `‖L(C_1, 1)‖ < 1.26 < 2 ≤ Ω`, `0.14 < Re L(C_3, 1)`,
`‖L(C_3, 1)‖ < 2.9`, from `LBounds.lean` with kernel-checked (`decide +kernel`) rational
certificates; hence `0 < ‖𝓛(1)²‖ = 4‖L(C_1,1)‖/Ω < 4` and `0 < ‖𝓛(3)²‖ = √3‖L(C_3,1)‖/Ω < 4`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open Complex Real Set MeasureTheory HurwitzZeta ZInQ.Contrib.HeckeFE ZInQ.Contrib.TYZLcal
open ZInQ.Contrib.HeckeAll

/-! ## `E = e^{−π/M²}` -/

theorem exp_bounds {M : ℕ} (hM : 0 < M) {l u : ℚ} (hl : (l : ℝ) ≤ 1 - 3.141593 / (M : ℝ) ^ 2)
    (hu : 1 / (1 + 3.141592 / (M : ℝ) ^ 2) ≤ (u : ℝ)) :
    (l : ℝ) ≤ Real.exp (-π / (M : ℝ) ^ 2) ∧ Real.exp (-π / (M : ℝ) ^ 2) ≤ u := by
  have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  have h1 := Real.pi_lt_d6
  have h2 := Real.pi_gt_d6
  constructor
  · refine hl.trans ?_
    have := Real.add_one_le_exp (-π / (M : ℝ) ^ 2)
    have : π / (M : ℝ) ^ 2 ≤ 3.141593 / (M : ℝ) ^ 2 := by gcongr
    rw [neg_div] at *; linarith
  · refine le_trans ?_ hu
    have he : Real.exp (-π / (M : ℝ) ^ 2) = 1 / Real.exp (π / (M : ℝ) ^ 2) := by
      rw [neg_div, Real.exp_neg, one_div]
    rw [he]
    have hx : 0 < 3.141592 / (M : ℝ) ^ 2 := by positivity
    have := Real.add_one_le_exp (π / (M : ℝ) ^ 2)
    have : 3.141592 / (M : ℝ) ^ 2 ≤ π / (M : ℝ) ^ 2 := by gcongr
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-! ## The two `L`-values as `Lsum` -/

theorem lValOne_one_eq_Lsum : ZInQ.Contrib.TYZDecomp.lValOne 1 =
    Lsum 4 (fun a b => uRe a b) (fun a b => uIm a b) := by
  rw [lValOne_one_eq, Lsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cU_eq, cC]; push_cast; rfl

/-- The real coefficient table of `L(C_3, s)`. -/
def cr3 (a b : ℕ) : ℤ := jac12 (a ^ 2 + b ^ 2) * uRe a b

/-- The imaginary coefficient table of `L(C_3, s)`. -/
def ci3 (a b : ℕ) : ℤ := jac12 (a ^ 2 + b ^ 2) * uIm a b

theorem lValOne_three_eq_Lsum : ZInQ.Contrib.TYZDecomp.lValOne 3 = Lsum 12 cr3 ci3 := by
  rw [lValOne_three_eq, Lsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [twChar_three_eq, cC, cr3, ci3]; push_cast; rfl

/-! ## Certificates (`decide +kernel`) -/

theorem w_one : ∑ j1 ∈ Finset.range 4, ∑ j2 ∈ Finset.range 4,
    (|(fun a b => uRe a b) j1 j2| + |(fun a b => uIm a b) j1 j2|) = 8 := by decide +kernel

theorem w_three : ∑ j1 ∈ Finset.range 12, ∑ j2 ∈ Finset.range 12, (|cr3 j1 j2| + |ci3 j1 j2|) = 64 := by
  decide +kernel

theorem cert_one_rl : (3 / 5 : ℚ) ≤ ∑ j1 ∈ Finset.range 4, ∑ j2 ∈ Finset.range 4,
    reClLo 4 (uRe j1 j2) (uIm j1 j2) j1 j2 (8036 / 10000) (836 / 1000) := by decide +kernel

theorem cert_one_rh : ∑ j1 ∈ Finset.range 4, ∑ j2 ∈ Finset.range 4,
    reClHi 4 (uRe j1 j2) (uIm j1 j2) j1 j2 (8036 / 10000) (836 / 1000) ≤ (71 / 100 : ℚ) := by
  decide +kernel

theorem cert_one_il : (-1 / 25 : ℚ) ≤ ∑ j1 ∈ Finset.range 4, ∑ j2 ∈ Finset.range 4,
    imClLo 4 (uRe j1 j2) (uIm j1 j2) j1 j2 (8036 / 10000) (836 / 1000) := by decide +kernel

theorem cert_one_ih : ∑ j1 ∈ Finset.range 4, ∑ j2 ∈ Finset.range 4,
    imClHi 4 (uRe j1 j2) (uIm j1 j2) j1 j2 (8036 / 10000) (836 / 1000) ≤ (1 / 25 : ℚ) := by
  decide +kernel

theorem cert_three_rl : (149 / 100 : ℚ) ≤ ∑ j1 ∈ Finset.range 12, ∑ j2 ∈ Finset.range 12,
    reClLo 12 (cr3 j1 j2) (ci3 j1 j2) j1 j2 (9781 / 10000) (9787 / 10000) := by decide +kernel

theorem cert_three_rh : ∑ j1 ∈ Finset.range 12, ∑ j2 ∈ Finset.range 12,
    reClHi 12 (cr3 j1 j2) (ci3 j1 j2) j1 j2 (9781 / 10000) (9787 / 10000) ≤ (153 / 100 : ℚ) := by
  decide +kernel

theorem cert_three_il : (-1 / 50 : ℚ) ≤ ∑ j1 ∈ Finset.range 12, ∑ j2 ∈ Finset.range 12,
    imClLo 12 (cr3 j1 j2) (ci3 j1 j2) j1 j2 (9781 / 10000) (9787 / 10000) := by decide +kernel

theorem cert_three_ih : ∑ j1 ∈ Finset.range 12, ∑ j2 ∈ Finset.range 12,
    imClHi 12 (cr3 j1 j2) (ci3 j1 j2) j1 j2 (9781 / 10000) (9787 / 10000) ≤ (1 / 50 : ℚ) := by
  decide +kernel

/-! ## From the enclosure to `‖L‖` -/

theorem norm_bounds_of {L S : ℂ} {ε rl rh il ih : ℝ} (hε : ‖L - S‖ ≤ ε) (hrl : rl ≤ S.re)
    (hrh : S.re ≤ rh) (hil : il ≤ S.im) (hih : S.im ≤ ih) :
    rl - ε ≤ L.re ∧ ‖L‖ ≤ max |rl| |rh| + max |il| |ih| + ε := by
  constructor
  · have := Complex.abs_re_le_norm (L - S)
    rw [Complex.sub_re] at this
    have := (abs_le.mp this).1
    linarith
  · have h1 : ‖L‖ ≤ ‖S‖ + ε := by
      have := norm_sub_norm_le L S; linarith
    have h2 := Complex.norm_le_abs_re_add_abs_im S
    have h3 : |S.re| ≤ max |rl| |rh| := by
      rw [abs_le']; constructor
      · exact hrh.trans ((le_abs_self rh).trans (le_max_right _ _))
      · have : -S.re ≤ -rl := by linarith
        exact this.trans ((neg_le_abs rl).trans (le_max_left _ _))
    have h4 : |S.im| ≤ max |il| |ih| := by
      rw [abs_le']; constructor
      · exact hih.trans ((le_abs_self ih).trans (le_max_right _ _))
      · have : -S.im ≤ -il := by linarith
        exact this.trans ((neg_le_abs il).trans (le_max_left _ _))
    linarith

theorem err_le {M : ℕ} (hM : 0 < M) (W : ℤ) (hW : 0 ≤ W) :
    (15.2 * Real.exp (-π) + 0.2487) / (4 * M) * W ≤ 1.0087 / (4 * M) * W := by
  have := exp_neg_pi_le
  have hM' : (0 : ℝ) < 4 * M := by positivity
  have hW' : (0 : ℝ) ≤ W := by exact_mod_cast hW
  gcongr
  linarith

/-- **`0.09 ≤ Re L(C_1, 1)` and `‖L(C_1, 1)‖ ≤ 1.26`.** -/
theorem lValOne_one_bounds : 0.09 ≤ (ZInQ.Contrib.TYZDecomp.lValOne 1).re ∧
    ‖ZInQ.Contrib.TYZDecomp.lValOne 1‖ ≤ 1.26 := by
  obtain ⟨hl, hu⟩ := exp_bounds (M := 4) (l := 8036 / 10000) (u := 836 / 1000) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨hε, hrl, hrh, hil, hih⟩ := Lsum_bounds 4 (by norm_num) (fun a b => uRe a b)
    (fun a b => uIm a b) (8036 / 10000) (836 / 1000) (by norm_num) (by exact_mod_cast hl)
    (by exact_mod_cast hu) 8 w_one _ _ _ _ cert_one_rl cert_one_rh cert_one_il cert_one_ih
  have he := err_le (M := 4) (by norm_num) 8 (by norm_num)
  rw [← lValOne_one_eq_Lsum] at hε
  obtain ⟨h1, h2⟩ := norm_bounds_of hε hrl hrh hil hih
  push_cast at h1 h2 he
  norm_num at h1 h2 he
  constructor
  · linarith
  · linarith

/-- **`0.14 ≤ Re L(C_3, 1)` and `‖L(C_3, 1)‖ ≤ 2.9`.** -/
theorem lValOne_three_bounds : 0.14 ≤ (ZInQ.Contrib.TYZDecomp.lValOne 3).re ∧
    ‖ZInQ.Contrib.TYZDecomp.lValOne 3‖ ≤ 2.9 := by
  obtain ⟨hl, hu⟩ := exp_bounds (M := 12) (l := 9781 / 10000) (u := 9787 / 10000) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨hε, hrl, hrh, hil, hih⟩ := Lsum_bounds 12 (by norm_num) cr3 ci3
    (9781 / 10000) (9787 / 10000) (by norm_num) (by exact_mod_cast hl)
    (by exact_mod_cast hu) 64 w_three _ _ _ _ cert_three_rl cert_three_rh cert_three_il cert_three_ih
  have he := err_le (M := 12) (by norm_num) 64 (by norm_num)
  rw [← lValOne_three_eq_Lsum] at hε
  obtain ⟨h1, h2⟩ := norm_bounds_of hε hrl hrh hil hih
  push_cast at h1 h2 he
  norm_num at h1 h2 he
  constructor
  · linarith
  · linarith

end ZInQ.Contrib.T21Proof
