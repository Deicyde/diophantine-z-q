import ZInQKernel.Contrib.TYZGenus.ShimuraQExp

/-!
# tyz-cm: x0-32's coordinate functions `x, y` are meromorphic at every cusp (proved)

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

Proves `EtaCuspGrowth` (`ShimuraModFn.lean`): for every `γ ∈ SL₂(ℤ)`, `x(γτ)` and `y(γτ)` are
`O(e^{12π Im τ})` as `Im τ → ∞`.

Method.
* `H(w) = |η(w)|⁴ Im w` is `SL₂(ℤ)`-invariant: `Δ = η²⁴` is a cusp form of weight 12 for
  `SL₂(ℤ)` (Mathlib's `CuspForm.discriminant`), so `|η(γw)|²⁴ = |cw + d|¹²|η(w)|²⁴`, and
  `Im(γw) = Im w/|cw + d|²`.
* For `δ ≥ 1`: `diag(δ, 1)·γ = γ'·[[g, t], [0, e]]` with `γ' ∈ SL₂(ℤ)`, `ge = δ` (Hermite), so
  `δ·γτ = γ'w` with `w = (gτ + t)/e`, `Im τ/δ ≤ Im w ≤ δ Im τ`. Hence
  `|η(δγτ)|⁴·δ·Im(γτ) = H(w)`: the automorphy factors cancel.
* For `Im w ≥ 1`: `m⁴e^{−π Im w/3} ≤ H(w) ≤ M⁴` (`η = q^{1/24}F(q)`, `m ≤ |F| ≤ M` on the compact
  disc `|q| ≤ e^{−2π}`).
* `|x(γτ) − 2|⁴·H(w₄)H(w₃₂)² = 64·H(w₂)²H(w₁₆)` and `|y(γτ)|⁴·H(w₄)²H(w₃₂)⁴ = 16·H(w₈)⁴H(w₁₆)²`,
  giving `|x − 2|⁴ ≤ K e^{68π Im τ/3}`, `|y|⁴ ≤ K e^{136π Im τ/3}`, both `≤ K e^{48π Im τ}`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open Complex Filter Topology Metric
open UpperHalfPlane hiding I

open scoped MatrixGroups

/-! ## The invariant `H(w) = |η(w)|⁴ Im w` -/

/-- `H(w) = |η(w)|⁴·Im w`. -/
def Hinv (w : UpperHalfPlane) : ℝ := ‖ModularForm.eta (w : ℂ)‖ ^ 4 * w.im

theorem Hinv_nonneg (w : UpperHalfPlane) : 0 ≤ Hinv w := by
  unfold Hinv; have := w.im_pos; positivity

theorem eta_pow_smul (γ : SL(2, ℤ)) (w : UpperHalfPlane) :
    ModularForm.eta ((γ • w : UpperHalfPlane) : ℂ) ^ 24 =
      denom γ w ^ 12 * ModularForm.eta (w : ℂ) ^ 24 := by
  have h := SlashInvariantForm.slash_action_eqn'' (k := 12) CuspForm.discriminant
    (γ := (γ : GL (Fin 2) ℝ)) (MonoidHom.mem_range.2 ⟨γ, rfl⟩) w
  simp only [CuspForm.coe_discriminant, ModularForm.discriminant] at h
  rw [ModularGroup.sl_moeb]
  exact h

/-- **`H` is `SL₂(ℤ)`-invariant.** -/
theorem Hinv_smul (γ : SL(2, ℤ)) (w : UpperHalfPlane) : Hinv (γ • w) = Hinv w := by
  have h24 := congrArg (‖·‖) (eta_pow_smul γ w)
  simp only [norm_pow, norm_mul] at h24
  have him := ModularGroup.im_smul_eq_div_normSq γ w
  rw [Complex.normSq_eq_norm_sq] at him
  have hd : ‖denom γ w‖ ≠ 0 := norm_ne_zero_iff.2 (denom_ne_zero _ _)
  refine (pow_left_inj₀ (Hinv_nonneg _) (Hinv_nonneg _) (by norm_num : (6 : ℕ) ≠ 0)).1 ?_
  unfold Hinv
  rw [him]
  have e1 : (‖ModularForm.eta ((γ • w : UpperHalfPlane) : ℂ)‖ ^ 4 *
      (w.im / ‖denom γ w‖ ^ 2)) ^ 6 =
      ‖ModularForm.eta ((γ • w : UpperHalfPlane) : ℂ)‖ ^ 24 * w.im ^ 6 / ‖denom γ w‖ ^ 12 := by
    field_simp
  rw [e1, h24]
  field_simp

/-! ## The Hermite decomposition `diag(δ, 1)·γ = γ'·[[g, t], [0, e]]` -/

theorem exists_hermite (a b c d δ : ℤ) (hdet : a * d - b * c = 1) (hδ : 0 < δ) :
    ∃ p u s v g t e : ℤ, p * v - u * s = 1 ∧ p * g = δ * a ∧ p * t + u * e = δ * b ∧
      s * g = c ∧ s * t + v * e = d ∧ 0 < g ∧ 0 < e ∧ g * e = δ := by
  set g : ℤ := (Int.gcd (δ * a) c : ℤ) with hg
  have hg0 : 0 < g := by
    rw [hg]
    have : Int.gcd (δ * a) c ≠ 0 := by
      intro h
      rw [Int.gcd_eq_zero_iff] at h
      have ha : a = 0 := by
        rcases mul_eq_zero.1 h.1 with h' | h'
        · omega
        · exact h'
      rw [ha, h.2] at hdet; simp at hdet
    positivity
  obtain ⟨p, hp⟩ : (g : ℤ) ∣ δ * a := Int.gcd_dvd_left _ _
  obtain ⟨s, hs⟩ : (g : ℤ) ∣ c := Int.gcd_dvd_right _ _
  have hcop : Int.gcd p s = 1 := by
    have h := Int.gcd_div_gcd_div_gcd (i := δ * a) (j := c) (by rw [hg] at hg0; exact_mod_cast hg0)
    have e1 : δ * a / (Int.gcd (δ * a) c : ℤ) = p := by
      rw [← hg, hp]; exact Int.mul_ediv_cancel_left _ hg0.ne'
    have e2 : c / (Int.gcd (δ * a) c : ℤ) = s := by
      rw [← hg, hs]; exact Int.mul_ediv_cancel_left _ hg0.ne'
    rwa [e1, e2] at h
  have hb := Int.gcd_eq_gcd_ab p s
  rw [hcop] at hb
  set v := Int.gcdA p s
  set u := -Int.gcdB p s
  have hB : p * v - u * s = 1 := by simp only [u]; linear_combination -hb
  refine ⟨p, u, s, v, g, v * δ * b - u * d, -s * δ * b + p * d, hB, by linear_combination -hp,
    by linear_combination δ * b * hB, by linear_combination -hs, by linear_combination d * hB,
    hg0, ?_, ?_⟩
  · have : g * (-s * δ * b + p * d) = δ := by
      linear_combination (δ * b) * hs - d * hp + δ * hdet
    by_contra hneg
    push_neg at hneg
    nlinarith
  · linear_combination (δ * b) * hs - d * hp + δ * hdet

/-- **`δ·γτ = γ'w` with `Im τ/δ ≤ Im w ≤ δ Im τ`.** -/
theorem exists_smul_decomp {δ : ℕ} (hδ : 0 < δ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ∃ (γ' : SL(2, ℤ)) (w : UpperHalfPlane), (δ : ℂ) * ((γ • τ : UpperHalfPlane) : ℂ) =
      ((γ' • w : UpperHalfPlane) : ℂ) ∧ τ.im / δ ≤ w.im ∧ w.im ≤ δ * τ.im := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨p, u, s, v, g, t, e, hB, hp, hpt, hs, hst, hg0, he0, hge⟩ :=
    exists_hermite (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) δ hdet (by exact_mod_cast hδ)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have heR : (0 : ℝ) < e := by exact_mod_cast he0
  have hgeR : (g : ℝ) * e = δ := by exact_mod_cast hge
  have hwim : 0 < (((g : ℂ) * τ + t) / e).im := by
    have : (((g : ℂ) * τ + t) / e).im = g * τ.im / e := by
      rw [show (e : ℂ) = ((e : ℝ) : ℂ) by simp, Complex.div_ofReal_im]
      simp
    rw [this]; have := τ.im_pos; positivity
  let w : UpperHalfPlane := ⟨((g : ℂ) * τ + t) / e, hwim⟩
  have hwim' : w.im = g * τ.im / e := by
    show (((g : ℂ) * τ + t) / e).im = _
    rw [show (e : ℂ) = ((e : ℝ) : ℂ) by simp, Complex.div_ofReal_im]
    simp
  let γ' : SL(2, ℤ) := ⟨!![p, u; s, v], by rw [Matrix.det_fin_two_of]; exact hB⟩
  refine ⟨γ', w, ?_, ?_, ?_⟩
  · rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
    simp only [γ', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      algebraMap_int_eq, eq_intCast, Int.cast_id]
    have hden : ((γ 1 0 : ℝ) : ℂ) * τ + ((γ 1 1 : ℝ) : ℂ) ≠ 0 := by
      have := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
      simpa [ModularGroup.denom_apply] using this
    have heC : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
    have h1 : ((p : ℝ) : ℂ) * (w : ℂ) + ((u : ℝ) : ℂ) =
        δ * (((γ 0 0 : ℝ) : ℂ) * τ + ((γ 0 1 : ℝ) : ℂ)) / e := by
      show ((p : ℝ) : ℂ) * (((g : ℂ) * τ + t) / e) + ((u : ℝ) : ℂ) = _
      field_simp
      have hp' : (p : ℂ) * g = δ * γ 0 0 := by exact_mod_cast hp
      have hpt' : (p : ℂ) * t + u * e = δ * γ 0 1 := by exact_mod_cast hpt
      push_cast
      linear_combination (τ : ℂ) * hp' + hpt'
    have h2 : ((s : ℝ) : ℂ) * (w : ℂ) + ((v : ℝ) : ℂ) =
        (((γ 1 0 : ℝ) : ℂ) * τ + ((γ 1 1 : ℝ) : ℂ)) / e := by
      show ((s : ℝ) : ℂ) * (((g : ℂ) * τ + t) / e) + ((v : ℝ) : ℂ) = _
      field_simp
      have hs' : (s : ℂ) * g = γ 1 0 := by exact_mod_cast hs
      have hst' : (s : ℂ) * t + v * e = γ 1 1 := by exact_mod_cast hst
      push_cast
      linear_combination (τ : ℂ) * hs' + hst'
    rw [h1, h2]
    field_simp
  · rw [hwim', div_le_div_iff₀ (by exact_mod_cast hδ) heR]
    have := τ.im_pos
    have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg0
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he0
    have h3 : (e : ℝ) ≤ g * δ := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 this.le
    nlinarith
  · rw [hwim', div_le_iff₀ heR]
    have := τ.im_pos
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he0
    have hgd : (g : ℝ) ≤ δ := by nlinarith
    have h3 : (g : ℝ) ≤ δ * e := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 this.le
    nlinarith

/-- **`|η(δγτ)|⁴·δ·Im(γτ) = H(w)`** with `Im τ/δ ≤ Im w ≤ δ Im τ`. -/
theorem etaD_norm_eq {δ : ℕ} (hδ : 0 < δ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ∃ w : UpperHalfPlane, ‖X0.etaD δ ((γ • τ : UpperHalfPlane) : ℂ)‖ ^ 4 * (δ * (γ • τ).im) =
      Hinv w ∧ τ.im / δ ≤ w.im ∧ w.im ≤ δ * τ.im := by
  obtain ⟨γ', w, hw, h1, h2⟩ := exists_smul_decomp hδ γ τ
  refine ⟨w, ?_, h1, h2⟩
  rw [← Hinv_smul γ' w]
  unfold Hinv X0.etaD
  rw [hw]
  congr 1
  have := congrArg Complex.im hw
  simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero] at this
  exact this

/-! ## Bounds for `H` -/

theorem eta_eq_prodF (z : ℂ) :
    ModularForm.eta z = Function.Periodic.qParam 24 z * X0.prodF (cexp (2 * Real.pi * I * z)) := by
  unfold ModularForm.eta X0.prodF
  simp_rw [ModularForm.eta_q_eq_pow]

theorem norm_qParam24_pow4 (w : UpperHalfPlane) :
    ‖Function.Periodic.qParam 24 (w : ℂ)‖ ^ 4 = Real.exp (-(Real.pi * w.im / 3)) := by
  rw [Function.Periodic.qParam, Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  ring

theorem norm_q_le (w : UpperHalfPlane) (hw : 1 ≤ w.im) :
    ‖cexp (2 * Real.pi * I * (w : ℂ))‖ ≤ Real.exp (-(2 * Real.pi)) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have : (2 * (Real.pi : ℂ) * I * (w : ℂ)).re = -(2 * Real.pi * w.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  nlinarith [Real.pi_pos]

theorem exists_prodF_bounds :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ q : ℂ, ‖q‖ ≤ Real.exp (-(2 * Real.pi)) →
      m ≤ ‖X0.prodF q‖ ∧ ‖X0.prodF q‖ ≤ M := by
  set r := Real.exp (-(2 * Real.pi))
  have hr1 : r < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr1
  have hc : ContinuousOn (fun q => ‖X0.prodF q‖) (closedBall (0 : ℂ) r) :=
    (ModularForm.differentiableOn_tprod_one_sub_pow.continuousOn.mono hsub).norm
  have hne : (closedBall (0 : ℂ) r).Nonempty := ⟨0, by simp [r, (Real.exp_pos _).le]⟩
  obtain ⟨q0, hq0, hmin⟩ := (isCompact_closedBall (0 : ℂ) r).exists_isMinOn hne hc
  obtain ⟨q1, hq1, hmax⟩ := (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn hne hc
  have hpos : 0 < ‖X0.prodF q0‖ :=
    norm_pos_iff.2 (prodF_ne_zero (by simpa using (mem_closedBall_zero_iff.1 hq0).trans_lt hr1))
  refine ⟨‖X0.prodF q0‖, ‖X0.prodF q0‖ + ‖X0.prodF q1‖, hpos, by positivity, fun q hq => ?_⟩
  have hq' : q ∈ closedBall (0 : ℂ) r := mem_closedBall_zero_iff.2 hq
  refine ⟨hmin hq', ?_⟩
  have := hmax hq'
  simp only [Set.mem_setOf_eq] at this
  linarith

theorem Hinv_bounds :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ w : UpperHalfPlane, 1 ≤ w.im →
      m * Real.exp (-(Real.pi * w.im / 3)) ≤ Hinv w ∧ Hinv w ≤ M := by
  obtain ⟨m, M, hm, hM, hb⟩ := exists_prodF_bounds
  refine ⟨m ^ 4, M ^ 4, by positivity, by positivity, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := hb _ (norm_q_le w hw)
  have hH : Hinv w = Real.exp (-(Real.pi * w.im / 3)) *
      ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 * w.im := by
    unfold Hinv
    rw [eta_eq_prodF, norm_mul, mul_pow, norm_qParam24_pow4]
  rw [hH]
  have hE := Real.exp_pos (-(Real.pi * w.im / 3))
  constructor
  · have : m ^ 4 ≤ ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 :=
      pow_le_pow_left₀ hm.le h1 4
    have hP : 0 ≤ ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 := by positivity
    calc m ^ 4 * Real.exp (-(Real.pi * w.im / 3))
        ≤ ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 * Real.exp (-(Real.pi * w.im / 3)) :=
          mul_le_mul_of_nonneg_right this hE.le
      _ = Real.exp (-(Real.pi * w.im / 3)) * ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 * 1 :=
          by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
  · -- `t·e^{−πt/3} ≤ t·e^{−t} ≤ 1`
    have hP : ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 ≤ M ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 4
    have ht : Real.exp (-(Real.pi * w.im / 3)) * w.im ≤ 1 := by
      have h3 : Real.exp (-(Real.pi * w.im / 3)) ≤ Real.exp (-w.im) := by
        apply Real.exp_le_exp.2
        have := Real.pi_gt_three
        nlinarith
      have h4 : w.im + 1 ≤ Real.exp w.im := Real.add_one_le_exp _
      have h5 : Real.exp (-w.im) * Real.exp w.im = 1 := by
        rw [← Real.exp_add]; simp
      have h6 : Real.exp (-w.im) * w.im ≤ 1 := by nlinarith [Real.exp_pos (-w.im)]
      nlinarith
    have hP0 : 0 ≤ ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 := by positivity
    calc Real.exp (-(Real.pi * w.im / 3)) * ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 * w.im
        = ‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4 *
          (Real.exp (-(Real.pi * w.im / 3)) * w.im) := by ring
      _ ≤ M ^ 4 * 1 := by gcongr
      _ = M ^ 4 := mul_one _

/-! ## Assembly -/

/-- For `Im τ ≥ 32` and `δ ∣ 32`: bounds on `A_δ = |η(δγτ)|⁴` through `H(w_δ)`. -/
theorem etaD_bounds {m M : ℝ} (hb : ∀ w : UpperHalfPlane, 1 ≤ w.im →
      m * Real.exp (-(Real.pi * w.im / 3)) ≤ Hinv w ∧ Hinv w ≤ M) (hm : 0 < m)
    {δ : ℕ} (hδ : 0 < δ) (hδ32 : δ ≤ 32) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (hτ : 32 ≤ τ.im) :
    ∃ Hδ : ℝ, ‖X0.etaD δ ((γ • τ : UpperHalfPlane) : ℂ)‖ ^ 4 * (δ * (γ • τ).im) = Hδ ∧
      m * Real.exp (-(Real.pi * (δ * τ.im) / 3)) ≤ Hδ ∧ Hδ ≤ M := by
  obtain ⟨w, hw, h1, h2⟩ := etaD_norm_eq hδ γ τ
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hw1 : 1 ≤ w.im := by
    refine le_trans ?_ h1
    rw [le_div_iff₀ hδR]
    have : (δ : ℝ) ≤ 32 := by exact_mod_cast hδ32
    linarith
  obtain ⟨hl, hu⟩ := hb w hw1
  refine ⟨Hinv w, hw, le_trans ?_ hl, hu⟩
  gcongr

theorem bigO_of_pow4 {f : UpperHalfPlane → ℂ} {K : ℝ} (hK : 0 ≤ K) (c : ℂ)
    (h : ∀ τ : UpperHalfPlane, 32 ≤ τ.im →
      ‖f τ - c‖ ^ 4 ≤ K * Real.exp (2 * Real.pi * (6 : ℕ) * τ.im) ^ 4) :
    f =O[atImInfty] fun τ => Real.exp (2 * Real.pi * (6 : ℕ) * τ.im) := by
  refine Asymptotics.IsBigO.of_bound (K + 1 + ‖c‖) ?_
  rw [Filter.eventually_iff, atImInfty_mem]
  refine ⟨32, fun τ hτ => ?_⟩
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs]
  set E := Real.exp (2 * Real.pi * (6 : ℕ) * τ.im)
  have hE1 : 1 ≤ E := Real.one_le_exp (by have := τ.im_pos; positivity)
  rw [abs_of_pos (Real.exp_pos _)]
  have h1 : ‖f τ - c‖ ≤ (K + 1) * E := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity) ?_
    calc ‖f τ - c‖ ^ 4 ≤ K * E ^ 4 := h τ hτ
      _ ≤ (K + 1) ^ 4 * E ^ 4 := by
          gcongr
          exact (by linarith : K ≤ K + 1).trans (le_self_pow₀ (by linarith) (by norm_num))
      _ = ((K + 1) * E) ^ 4 := by ring
  calc ‖f τ‖ = ‖(f τ - c) + c‖ := by ring_nf
    _ ≤ ‖f τ - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ (K + 1) * E + ‖c‖ * E := by gcongr; nlinarith [norm_nonneg c]
    _ = (K + 1 + ‖c‖) * E := by ring

theorem exp_combine (T : ℝ) (hT : 0 ≤ T) (a : ℝ) (ha : a ≤ 144) :
    Real.exp (Real.pi * a * T / 3) ≤ Real.exp (2 * Real.pi * (6 : ℕ) * T) ^ 4 := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  push_cast
  have := Real.pi_pos
  nlinarith [mul_nonneg this.le hT]

/-- **`x(γτ) = O(e^{12π Im τ})`.** -/
theorem xC_growth (γ : SL(2, ℤ)) :
    (fun τ : UpperHalfPlane => X0.xC (γ • τ : UpperHalfPlane)) =O[atImInfty]
      fun τ => Real.exp (2 * Real.pi * (6 : ℕ) * τ.im) := by
  obtain ⟨m, M, hm, hM, hb⟩ := Hinv_bounds
  refine bigO_of_pow4 (K := 64 * M ^ 3 / m ^ 3) (by positivity) 2 fun τ hτ => ?_
  set z : ℂ := ((γ • τ : UpperHalfPlane) : ℂ)
  set I0 := (γ • τ).im
  have hI : 0 < I0 := (γ • τ).im_pos
  obtain ⟨H2, e2, -, u2⟩ := etaD_bounds hb hm (δ := 2) (by norm_num) (by norm_num) γ τ hτ
  obtain ⟨H16, e16, -, u16⟩ := etaD_bounds hb hm (δ := 16) (by norm_num) (by norm_num) γ τ hτ
  obtain ⟨H4, e4, l4, -⟩ := etaD_bounds hb hm (δ := 4) (by norm_num) (by norm_num) γ τ hτ
  obtain ⟨H32, e32, l32, -⟩ := etaD_bounds hb hm (δ := 32) (by norm_num) (by norm_num) γ τ hτ
  have n2 := X0.etaD_ne_zero (d := 2) (by norm_num) (γ • τ)
  have n4 := X0.etaD_ne_zero (d := 4) (by norm_num) (γ • τ)
  have n16 := X0.etaD_ne_zero (d := 16) (by norm_num) (γ • τ)
  have n32 := X0.etaD_ne_zero (d := 32) (by norm_num) (γ • τ)
  have hx : X0.xC z - 2 = X0.etaD 2 z ^ 2 * X0.etaD 16 z / (X0.etaD 4 z * X0.etaD 32 z ^ 2) := by
    unfold X0.xC; ring
  rw [hx]
  set a2 := ‖X0.etaD 2 z‖
  set a4 := ‖X0.etaD 4 z‖
  set a16 := ‖X0.etaD 16 z‖
  set a32 := ‖X0.etaD 32 z‖
  have p4 : 0 < a4 := norm_pos_iff.2 n4
  have p32 : 0 < a32 := norm_pos_iff.2 n32
  have hnorm : ‖X0.etaD 2 z ^ 2 * X0.etaD 16 z / (X0.etaD 4 z * X0.etaD 32 z ^ 2)‖ =
      a2 ^ 2 * a16 / (a4 * a32 ^ 2) := by
    simp only [norm_div, norm_mul, norm_pow, a2, a4, a16, a32]
  rw [hnorm]
  -- the identity `|x − 2|⁴·H₄H₃₂² = 64·H₂²H₁₆`
  have hid : (a2 ^ 2 * a16 / (a4 * a32 ^ 2)) ^ 4 * (H4 * H32 ^ 2) = 64 * (H2 ^ 2 * H16) := by
    rw [← e2, ← e4, ← e16, ← e32]
    push_cast
    field_simp
    ring
  have hT := τ.im_pos
  set T := τ.im
  have hL : m * Real.exp (-(Real.pi * (4 * T) / 3)) * (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 2
      ≤ H4 * H32 ^ 2 := by
    have hl4 : m * Real.exp (-(Real.pi * ((4 : ℕ) * T) / 3)) ≤ H4 := l4
    have hl32 : m * Real.exp (-(Real.pi * ((32 : ℕ) * T) / 3)) ≤ H32 := l32
    push_cast at hl4 hl32
    have : 0 ≤ m * Real.exp (-(Real.pi * (32 * T) / 3)) := by positivity
    have h4' : 0 ≤ H4 := by rw [← e4]; positivity
    gcongr
  have hU : H2 ^ 2 * H16 ≤ M ^ 2 * M := by
    have h2' : 0 ≤ H2 := by rw [← e2]; positivity
    have h16' : 0 ≤ H16 := by rw [← e16]; positivity
    gcongr
  have hLpos : 0 < m * Real.exp (-(Real.pi * (4 * T) / 3)) *
      (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 2 := by positivity
  have hX0 : 0 ≤ (a2 ^ 2 * a16 / (a4 * a32 ^ 2)) ^ 4 := by positivity
  have hbound : (a2 ^ 2 * a16 / (a4 * a32 ^ 2)) ^ 4 ≤
      64 * (M ^ 2 * M) / (m * Real.exp (-(Real.pi * (4 * T) / 3)) *
        (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 2) := by
    rw [le_div_iff₀ hLpos]
    calc _ ≤ (a2 ^ 2 * a16 / (a4 * a32 ^ 2)) ^ 4 * (H4 * H32 ^ 2) := by gcongr
      _ = 64 * (H2 ^ 2 * H16) := hid
      _ ≤ 64 * (M ^ 2 * M) := by gcongr
  refine hbound.trans ?_
  have hexp : 64 * (M ^ 2 * M) / (m * Real.exp (-(Real.pi * (4 * T) / 3)) *
      (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 2) =
      64 * M ^ 3 / m ^ 3 * Real.exp (Real.pi * 68 * T / 3) := by
    have hE : Real.exp (Real.pi * 68 * T / 3) = (Real.exp (-(Real.pi * (4 * T) / 3)) *
        Real.exp (-(Real.pi * (32 * T) / 3)) ^ 2)⁻¹ := by
      rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_neg]; congr 1; ring
    rw [hE]
    field_simp
  rw [hexp]
  exact mul_le_mul_of_nonneg_left (exp_combine T hT.le 68 (by norm_num)) (by positivity)

/-- **`y(γτ) = O(e^{12π Im τ})`.** -/
theorem yC_growth (γ : SL(2, ℤ)) :
    (fun τ : UpperHalfPlane => X0.yC (γ • τ : UpperHalfPlane)) =O[atImInfty]
      fun τ => Real.exp (2 * Real.pi * (6 : ℕ) * τ.im) := by
  obtain ⟨m, M, hm, hM, hb⟩ := Hinv_bounds
  refine bigO_of_pow4 (K := 16 * M ^ 6 / m ^ 6) (by positivity) 0 fun τ hτ => ?_
  set z : ℂ := ((γ • τ : UpperHalfPlane) : ℂ)
  obtain ⟨H8, e8, -, u8⟩ := etaD_bounds hb hm (δ := 8) (by norm_num) (by norm_num) γ τ hτ
  obtain ⟨H16, e16, -, u16⟩ := etaD_bounds hb hm (δ := 16) (by norm_num) (by norm_num) γ τ hτ
  obtain ⟨H4, e4, l4, -⟩ := etaD_bounds hb hm (δ := 4) (by norm_num) (by norm_num) γ τ hτ
  obtain ⟨H32, e32, l32, -⟩ := etaD_bounds hb hm (δ := 32) (by norm_num) (by norm_num) γ τ hτ
  have n4 := X0.etaD_ne_zero (d := 4) (by norm_num) (γ • τ)
  have n32 := X0.etaD_ne_zero (d := 32) (by norm_num) (γ • τ)
  have hI : 0 < (γ • τ).im := (γ • τ).im_pos
  rw [sub_zero]
  set a8 := ‖X0.etaD 8 z‖
  set a4 := ‖X0.etaD 4 z‖
  set a16 := ‖X0.etaD 16 z‖
  set a32 := ‖X0.etaD 32 z‖
  have p4 : 0 < a4 := norm_pos_iff.2 n4
  have p32 : 0 < a32 := norm_pos_iff.2 n32
  have hnorm : ‖X0.yC z‖ = a8 ^ 4 * a16 ^ 2 / (a4 ^ 2 * a32 ^ 4) := by
    unfold X0.yC
    simp only [norm_neg, norm_div, norm_mul, norm_pow, a8, a4, a16, a32]
  rw [hnorm]
  have hid : (a8 ^ 4 * a16 ^ 2 / (a4 ^ 2 * a32 ^ 4)) ^ 4 * (H4 ^ 2 * H32 ^ 4) =
      16 * (H8 ^ 4 * H16 ^ 2) := by
    rw [← e8, ← e4, ← e16, ← e32]
    push_cast
    field_simp
    ring
  have hT := τ.im_pos
  set T := τ.im
  have hL : (m * Real.exp (-(Real.pi * (4 * T) / 3))) ^ 2 *
      (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 4 ≤ H4 ^ 2 * H32 ^ 4 := by
    have hl4 : m * Real.exp (-(Real.pi * ((4 : ℕ) * T) / 3)) ≤ H4 := l4
    have hl32 : m * Real.exp (-(Real.pi * ((32 : ℕ) * T) / 3)) ≤ H32 := l32
    push_cast at hl4 hl32
    have : 0 ≤ m * Real.exp (-(Real.pi * (32 * T) / 3)) := by positivity
    have : 0 ≤ m * Real.exp (-(Real.pi * (4 * T) / 3)) := by positivity
    gcongr
  have hU : H8 ^ 4 * H16 ^ 2 ≤ M ^ 4 * M ^ 2 := by
    have h8' : 0 ≤ H8 := by rw [← e8]; positivity
    have h16' : 0 ≤ H16 := by rw [← e16]; positivity
    gcongr
  have hLpos : 0 < (m * Real.exp (-(Real.pi * (4 * T) / 3))) ^ 2 *
      (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 4 := by positivity
  have hbound : (a8 ^ 4 * a16 ^ 2 / (a4 ^ 2 * a32 ^ 4)) ^ 4 ≤
      16 * (M ^ 4 * M ^ 2) / ((m * Real.exp (-(Real.pi * (4 * T) / 3))) ^ 2 *
        (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 4) := by
    rw [le_div_iff₀ hLpos]
    calc _ ≤ (a8 ^ 4 * a16 ^ 2 / (a4 ^ 2 * a32 ^ 4)) ^ 4 * (H4 ^ 2 * H32 ^ 4) := by gcongr
      _ = 16 * (H8 ^ 4 * H16 ^ 2) := hid
      _ ≤ 16 * (M ^ 4 * M ^ 2) := by gcongr
  refine hbound.trans ?_
  have hexp : 16 * (M ^ 4 * M ^ 2) / ((m * Real.exp (-(Real.pi * (4 * T) / 3))) ^ 2 *
      (m * Real.exp (-(Real.pi * (32 * T) / 3))) ^ 4) =
      16 * M ^ 6 / m ^ 6 * Real.exp (Real.pi * 136 * T / 3) := by
    have hE : Real.exp (Real.pi * 136 * T / 3) = (Real.exp (-(Real.pi * (4 * T) / 3)) ^ 2 *
        Real.exp (-(Real.pi * (32 * T) / 3)) ^ 4)⁻¹ := by
      rw [show ∀ x : ℝ, x ^ 4 = x * x * x * x from fun x => by ring, sq, ← Real.exp_add,
        ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_neg]
      congr 1; ring
    rw [hE]
    field_simp
  rw [hexp]
  exact mul_le_mul_of_nonneg_left (exp_combine T hT.le 136 (by norm_num)) (by positivity)

/-- **`EtaCuspGrowth`, proved**: `x, y` are meromorphic at every cusp (`k = 6`). -/
theorem etaCuspGrowth : EtaCuspGrowth := fun γ => ⟨6, xC_growth γ, yC_growth γ⟩

/-- **The CM leaf from the general Shimura reciprocity law for `ℚ(X₀(N))` and x0-32's
`Γ₀(32)`-invariance leaf** (cusp growth and the `q`-expansions are proved). -/
theorem cmFieldOfDefinition_of_modFn_inv (hS : ShimuraReciprocityModFn)
    (hI : X0.EtaModelInvariant) :
    ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition RingClass.ringClassFieldD :=
  cmFieldOfDefinition_of_modFn' hS hI etaCuspGrowth

end ZInQ.Contrib.TYZGenus.Shimura
