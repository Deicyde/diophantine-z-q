import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilTheta
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

noncomputable section

open Complex Filter Topology
open scoped Real MatrixGroups ModularForm

namespace ZInQ.GZWeil

/-! ## J1. Transformation laws of `θ₂, θ₃, θ₄` -/

theorem jacobiTheta₂_add_one_right (z τ : ℂ) :
    jacobiTheta₂ z (τ + 1) = jacobiTheta₂ (z + 1 / 2) τ := by
  refine tsum_congr fun n => ?_
  simp only [jacobiTheta₂_term]
  rw [Complex.exp_eq_exp_iff_exists_int]
  obtain ⟨m, hm⟩ := Int.even_mul_pred_self n
  refine ⟨m, ?_⟩
  have hm' : ((n : ℂ) * ((n : ℂ) - 1)) = (m : ℂ) + m := by exact_mod_cast hm
  linear_combination (π * I) * hm'

theorem thetaThree_add_one (t : ℂ) : thetaThree (t + 1) = thetaFour t := by
  rw [thetaThree, thetaFour, jacobiTheta₂_add_one_right, zero_add]

theorem thetaFour_add_one (t : ℂ) : thetaFour (t + 1) = thetaThree t := by
  rw [thetaThree, thetaFour, jacobiTheta₂_add_one_right]
  norm_num
  exact jacobiTheta₂_add_left 0 t ▸ by simp

theorem thetaTwo_add_one (t : ℂ) : thetaTwo (t + 1) = cexp (π * I / 4) * thetaTwo t := by
  rw [thetaTwo, thetaTwo, jacobiTheta₂_add_one_right,
    show (t + 1) / 2 + 1 / 2 = t / 2 + 1 by ring, jacobiTheta₂_add_left, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

/-- `(−iτ)^{1/2}` squared. -/
theorem sqrt_factor_sq (τ : ℂ) : ((-I * τ) ^ (1 / 2 : ℂ)) ^ 2 = -I * τ := by
  rw [show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
  exact Complex.cpow_nat_inv_pow _ two_ne_zero

theorem sqrt_factor_ne_zero {τ : ℂ} (hτ : τ ≠ 0) : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  exact Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ)

theorem thetaThree_S {τ : ℂ} (hτ : τ ≠ 0) :
    thetaThree (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaThree τ := by
  have h := jacobiTheta₂_functional_equation 0 τ
  simp only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Complex.exp_zero, mul_one] at h
  rw [thetaThree, thetaThree, h]
  field_simp [sqrt_factor_ne_zero hτ]

theorem thetaTwo_S {τ : ℂ} (hτ : τ ≠ 0) :
    thetaTwo (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaFour τ := by
  have h := jacobiTheta₂_functional_equation (1 / 2) τ
  rw [thetaTwo, thetaFour, h, show (-1 / τ) / 2 = -((1 / 2) / τ) by ring, jacobiTheta₂_neg_left]
  have hs := sqrt_factor_ne_zero hτ
  have he : cexp (π * I * (-1 / τ) / 4) = cexp (-π * I * (1 / 2) ^ 2 / τ) := by
    congr 1; field_simp; ring
  rw [he]
  field_simp

theorem thetaThree_S_sq {τ : ℂ} (hτ : τ ≠ 0) :
    thetaThree (-1 / τ) ^ 2 = -I * τ * thetaThree τ ^ 2 := by
  rw [thetaThree_S hτ, mul_pow, sqrt_factor_sq]

theorem thetaTwo_S_sq {τ : ℂ} (hτ : τ ≠ 0) :
    thetaTwo (-1 / τ) ^ 2 = -I * τ * thetaFour τ ^ 2 := by
  rw [thetaTwo_S hτ, mul_pow, sqrt_factor_sq]

theorem thetaFour_S_sq {τ : ℂ} (hτ : τ ≠ 0) :
    thetaFour (-1 / τ) ^ 2 = -I * τ * thetaTwo τ ^ 2 := by
  have hτ' : (-1 / τ) ≠ 0 := by simp [hτ]
  have h := thetaTwo_S_sq hτ'
  rw [show -1 / (-1 / τ) = τ by field_simp] at h
  rw [h]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring


/-! ## J2. Nonvanishing and the laws of the logarithmic derivatives -/

theorem im_neg_inv_pos {t : ℂ} (ht : 0 < t.im) : 0 < (-1 / t).im := by
  have h := (UpperHalfPlane.mk t ht).im_inv_neg_coe_pos
  simpa [neg_div, div_eq_mul_inv] using h

theorem ne_zero_of_im_pos {t : ℂ} (ht : 0 < t.im) : t ≠ 0 := by
  rintro rfl; simp at ht

theorem thetaThree_ne_zero {t : ℂ} (ht : 0 < t.im) : thetaThree t ≠ 0 := by
  rw [thetaThree, ZInQ.GZTheta.jacobiTheta₂_eq_jtpP ht]
  simpa using ZInQ.GZTheta.jtpP_ne_zero_of_real ht 0

theorem thetaFour_ne_zero {t : ℂ} (ht : 0 < t.im) : thetaFour t ≠ 0 := by
  rw [thetaFour, ZInQ.GZTheta.jacobiTheta₂_eq_jtpP ht]
  have := ZInQ.GZTheta.jtpP_ne_zero_of_real ht (1 / 2)
  push_cast at this
  exact this

theorem thetaTwo_ne_zero {t : ℂ} (ht : 0 < t.im) : thetaTwo t ≠ 0 := by
  have hτ := im_neg_inv_pos ht
  have h := thetaTwo_S_sq (ne_zero_of_im_pos hτ)
  rw [show -1 / (-1 / t) = t by field_simp [ne_zero_of_im_pos ht]] at h
  intro h0
  rw [h0] at h
  have : -I * (-1 / t) * thetaFour (-1 / t) ^ 2 ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) ?_)
      (pow_ne_zero _ (thetaFour_ne_zero hτ))
    exact ne_zero_of_im_pos hτ
  exact this (by rw [← h]; ring)

theorem differentiableAt_thetaFour {t : ℂ} (ht : 0 < t.im) : DifferentiableAt ℂ thetaFour t :=
  differentiableAt_jacobiTheta₂_snd (1 / 2) ht

/-- Logarithmic derivatives `θ'/θ`. -/
def LA (t : ℂ) : ℂ := deriv thetaTwo t / thetaTwo t
def LB (t : ℂ) : ℂ := deriv thetaThree t / thetaThree t
def LC (t : ℂ) : ℂ := deriv thetaFour t / thetaFour t

theorem LB_add_one (t : ℂ) : LB (t + 1) = LC t := by
  have hd : deriv thetaFour t = deriv thetaThree (t + 1) := by
    rw [← deriv_comp_add_const]; congr 1; funext s; exact (thetaThree_add_one s).symm
  rw [LB, LC, hd, thetaThree_add_one]

theorem LC_add_one (t : ℂ) : LC (t + 1) = LB t := by
  have hd : deriv thetaThree t = deriv thetaFour (t + 1) := by
    rw [← deriv_comp_add_const]; congr 1; funext s; exact (thetaFour_add_one s).symm
  rw [LB, LC, hd, thetaFour_add_one]

theorem LA_add_one (t : ℂ) : LA (t + 1) = LA t := by
  have hc : cexp (π * I / 4) ≠ 0 := Complex.exp_ne_zero _
  have hf : (fun s => thetaTwo (s + 1)) = fun s => cexp (π * I / 4) * thetaTwo s :=
    funext thetaTwo_add_one
  have hd : deriv thetaTwo (t + 1) = cexp (π * I / 4) * deriv thetaTwo t := by
    rw [← deriv_comp_add_const, hf, deriv_const_mul_field']
  rw [LA, LA, hd, thetaTwo_add_one]
  by_cases h0 : thetaTwo t = 0
  · simp [h0]
  · field_simp

/-- **The `S`-law of a logarithmic derivative.** If `g(−1/s)² = −is h(s)²` for `s ≠ 0`, then
`g'/g (−1/t) = t/2 + t² h'/h (t)`. -/
theorem log_deriv_S {g h : ℂ → ℂ} (hgh : ∀ s : ℂ, s ≠ 0 → g (-1 / s) ^ 2 = -I * s * h s ^ 2)
    {t : ℂ} (ht0 : t ≠ 0) (hg : DifferentiableAt ℂ g (-1 / t)) (hh : DifferentiableAt ℂ h t)
    (hh0 : h t ≠ 0) :
    deriv g (-1 / t) / g (-1 / t) = t / 2 + t ^ 2 * (deriv h t / h t) := by
  have hinv : HasDerivAt (fun s : ℂ => -1 / s) (1 / t ^ 2) t := by
    have := (hasDerivAt_inv ht0).const_mul (-1 : ℂ)
    convert this using 1
    · funext s; ring
    · field_simp
  have h1 : HasDerivAt (fun s => g (-1 / s) ^ 2)
      (2 * g (-1 / t) ^ (2 - 1) * (deriv g (-1 / t) * (1 / t ^ 2))) t :=
    (hg.hasDerivAt.comp t hinv).pow 2
  have h2 : HasDerivAt (fun s => -I * s * h s ^ 2)
      (-I * 1 * h t ^ 2 + -I * t * (2 * h t ^ (2 - 1) * deriv h t)) t :=
    ((hasDerivAt_id t).const_mul (-I)).mul (hh.hasDerivAt.pow 2)
  have hev : (fun s => g (-1 / s) ^ 2) =ᶠ[𝓝 t] fun s => -I * s * h s ^ 2 := by
    filter_upwards [isOpen_ne.mem_nhds ht0] with s hs using hgh s hs
  have heq := (h1.congr_of_eventuallyEq hev.symm).unique h2
  have hsq := hgh t ht0
  have hg0 : g (-1 / t) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsq
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) ht0) (pow_ne_zero _ hh0) hsq.symm
  generalize g (-1 / t) = G at heq hsq hg0 ⊢
  generalize deriv g (-1 / t) = G' at heq ⊢
  generalize h t = H at heq hsq hh0 ⊢
  generalize deriv h t = H' at heq ⊢
  norm_num at heq
  have heq2 : 2 * G * G' = t ^ 2 * (-(I * H ^ 2) + -(I * t * (2 * H * H'))) := by
    rw [← heq]; field_simp
  have key : G' = G * (t * H + 2 * t ^ 2 * H') / (2 * H) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hh0)]
    apply mul_left_cancel₀ hg0
    linear_combination H * heq2 - (t * H + 2 * t ^ 2 * H') * hsq
  rw [key]
  field_simp


/-! ## J3. The three differences `E₁, E₂, E₃` and their symmetric functions -/

theorem LB_S {t : ℂ} (ht : 0 < t.im) : LB (-1 / t) = t / 2 + t ^ 2 * LB t :=
  log_deriv_S (fun _ hs => thetaThree_S_sq hs) (ne_zero_of_im_pos ht)
    (differentiableAt_thetaThree (im_neg_inv_pos ht)) (differentiableAt_thetaThree ht)
    (thetaThree_ne_zero ht)

theorem LA_S {t : ℂ} (ht : 0 < t.im) : LA (-1 / t) = t / 2 + t ^ 2 * LC t :=
  log_deriv_S (fun _ hs => thetaTwo_S_sq hs) (ne_zero_of_im_pos ht)
    (differentiableAt_thetaTwo (im_neg_inv_pos ht)) (differentiableAt_thetaFour ht)
    (thetaFour_ne_zero ht)

theorem LC_S {t : ℂ} (ht : 0 < t.im) : LC (-1 / t) = t / 2 + t ^ 2 * LA t :=
  log_deriv_S (fun _ hs => thetaFour_S_sq hs) (ne_zero_of_im_pos ht)
    (differentiableAt_thetaFour (im_neg_inv_pos ht)) (differentiableAt_thetaTwo ht)
    (thetaTwo_ne_zero ht)

theorem pow4_of_sq {a b c : ℂ} (h : a ^ 2 = -I * c * b ^ 2) : a ^ 4 = -c ^ 2 * b ^ 4 := by
  have : a ^ 4 = (a ^ 2) ^ 2 := by ring
  rw [this, h]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem thetaTwo_add_one_pow4 (t : ℂ) : thetaTwo (t + 1) ^ 4 = -thetaTwo t ^ 4 := by
  rw [thetaTwo_add_one, mul_pow, ← Complex.exp_nat_mul]
  have : cexp (((4 : ℕ) : ℂ) * (π * I / 4)) = -1 := by
    rw [show ((4 : ℕ) : ℂ) * (π * I / 4) = π * I by push_cast; ring]
    exact Complex.exp_pi_mul_I
  rw [this]; ring

def E1 (t : ℂ) : ℂ := LB t - LA t + π * I / 4 * thetaFour t ^ 4
def E2 (t : ℂ) : ℂ := LB t - LC t - π * I / 4 * thetaTwo t ^ 4
def E3 (t : ℂ) : ℂ := LA t - LC t - π * I / 4 * thetaThree t ^ 4

theorem E1_S {t : ℂ} (ht : 0 < t.im) : E1 (-1 / t) = t ^ 2 * E2 t := by
  have h4 := pow4_of_sq (thetaFour_S_sq (ne_zero_of_im_pos ht))
  rw [E1, E2, LB_S ht, LA_S ht, h4]; ring

theorem E2_S {t : ℂ} (ht : 0 < t.im) : E2 (-1 / t) = t ^ 2 * E1 t := by
  have h4 := pow4_of_sq (thetaTwo_S_sq (ne_zero_of_im_pos ht))
  rw [E1, E2, LB_S ht, LC_S ht, h4]; ring

theorem E3_S {t : ℂ} (ht : 0 < t.im) : E3 (-1 / t) = -(t ^ 2 * E3 t) := by
  have h4 := pow4_of_sq (thetaThree_S_sq (ne_zero_of_im_pos ht))
  simp only [E3]
  rw [LA_S ht, LC_S ht, h4]; ring

theorem E1_T (t : ℂ) : E1 (t + 1) = -E3 t := by
  rw [E1, E3, LB_add_one, LA_add_one, thetaFour_add_one]; ring

theorem E2_T (t : ℂ) : E2 (t + 1) = -E2 t := by
  simp only [E2]
  rw [LB_add_one, LC_add_one, thetaTwo_add_one_pow4]; ring

theorem E3_T (t : ℂ) : E3 (t + 1) = -E1 t := by
  rw [E1, E3, LA_add_one, LC_add_one, thetaThree_add_one]; ring

def Psym (t : ℂ) : ℂ := E1 t ^ 2 + E2 t ^ 2 + E3 t ^ 2
def Rsym (t : ℂ) : ℂ := E1 t ^ 2 * E2 t ^ 2 + E2 t ^ 2 * E3 t ^ 2 + E3 t ^ 2 * E1 t ^ 2

theorem Psym_S {t : ℂ} (ht : 0 < t.im) : Psym (-1 / t) = t ^ 4 * Psym t := by
  rw [Psym, Psym, E1_S ht, E2_S ht, E3_S ht]; ring

theorem Rsym_S {t : ℂ} (ht : 0 < t.im) : Rsym (-1 / t) = t ^ 8 * Rsym t := by
  rw [Rsym, Rsym, E1_S ht, E2_S ht, E3_S ht]; ring

theorem Psym_T (t : ℂ) : Psym (t + 1) = Psym t := by
  rw [Psym, Psym, E1_T, E2_T, E3_T]; ring

theorem Rsym_T (t : ℂ) : Rsym (t + 1) = Rsym t := by
  rw [Rsym, Rsym, E1_T, E2_T, E3_T]; ring

/-! ## J4. Slash invariance under `SL(2, ℤ)` -/

open ModularGroup in
theorem slash_invariant_of_S_T {F : ℂ → ℂ} {k : ℕ}
    (hS : ∀ t : ℂ, 0 < t.im → F (-1 / t) = t ^ k * F t) (hT : ∀ t : ℂ, F (t + 1) = F t) :
    ∀ γ : SL(2, ℤ), (fun τ : UpperHalfPlane => F τ) ∣[(k : ℤ)] γ = fun τ : UpperHalfPlane => F τ := by
  apply SlashInvariantForm.slash_action_generators_SL2Z
  · ext τ
    rw [ModularForm.SL_slash_def]
    simp only
    rw [UpperHalfPlane.modular_S_smul, ModularGroup.denom_S]
    show F ((-(τ : ℂ))⁻¹) * (τ : ℂ) ^ (-(k : ℤ)) = F τ
    have h := hS τ τ.im_pos
    rw [show (-(τ : ℂ))⁻¹ = -1 / τ by ring, h]
    have hτ : (τ : ℂ) ≠ 0 := ne_zero_of_im_pos τ.im_pos
    rw [zpow_neg, zpow_natCast]
    field_simp
  · ext τ
    rw [ModularForm.SL_slash_def]
    simp only
    rw [UpperHalfPlane.modular_T_smul]
    have hd : UpperHalfPlane.denom (ModularGroup.T : GL (Fin 2) ℝ) τ = 1 := by
      rw [ModularGroup.denom_apply]
      simp [ModularGroup.coe_T]
    rw [hd, one_zpow, mul_one, UpperHalfPlane.coe_vadd, add_comm]
    simp only [Complex.ofReal_one]
    exact hT τ


/-! ## J5. Analyticity on `ℍ` -/

theorem U_isOpen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im

/-- `u(t) = θ(t/2; t) = e^{−πit/4} θ₂(t)`. -/
def uTheta (t : ℂ) : ℂ := jacobiTheta₂ (t / 2) t

theorem differentiableAt_uTheta {t : ℂ} (ht : 0 < t.im) : DifferentiableAt ℂ uTheta t := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (s / 2, s)) t :=
    (differentiableAt_id.div_const 2).prodMk differentiableAt_id
  have h2 := (hasFDerivAt_jacobiTheta₂ (t / 2) ht).differentiableAt
  exact DifferentiableAt.comp (f := fun s : ℂ => (s / 2, s))
    (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) t h2 h1

theorem thetaTwo_eq (t : ℂ) : thetaTwo t = cexp (π * I * t / 4) * uTheta t := rfl

theorem analyticOnNhd_of_diff {f : ℂ → ℂ} (hf : ∀ t : ℂ, 0 < t.im → DifferentiableAt ℂ f t) :
    AnalyticOnNhd ℂ f {w : ℂ | 0 < w.im} :=
  DifferentiableOn.analyticOnNhd (f := f) (s := {w : ℂ | 0 < w.im})
    (fun t ht => (hf t ht).differentiableWithinAt) U_isOpen

theorem analyticAt_LA {t : ℂ} (ht : 0 < t.im) : AnalyticAt ℂ LA t := by
  have h := analyticOnNhd_of_diff (fun _ hs => differentiableAt_thetaTwo hs)
  exact ((h t ht).deriv).div (h t ht) (thetaTwo_ne_zero ht)

theorem analyticAt_LB {t : ℂ} (ht : 0 < t.im) : AnalyticAt ℂ LB t := by
  have h := analyticOnNhd_of_diff (fun _ hs => differentiableAt_thetaThree hs)
  exact ((h t ht).deriv).div (h t ht) (thetaThree_ne_zero ht)

theorem analyticAt_LC {t : ℂ} (ht : 0 < t.im) : AnalyticAt ℂ LC t := by
  have h := analyticOnNhd_of_diff (fun _ hs => differentiableAt_thetaFour hs)
  exact ((h t ht).deriv).div (h t ht) (thetaFour_ne_zero ht)

theorem analyticAt_thetaTwo {t : ℂ} (ht : 0 < t.im) : AnalyticAt ℂ thetaTwo t :=
  analyticOnNhd_of_diff (fun _ hs => differentiableAt_thetaTwo hs) t ht
theorem analyticAt_thetaThree {t : ℂ} (ht : 0 < t.im) : AnalyticAt ℂ thetaThree t :=
  analyticOnNhd_of_diff (fun _ hs => differentiableAt_thetaThree hs) t ht
theorem analyticAt_thetaFour {t : ℂ} (ht : 0 < t.im) : AnalyticAt ℂ thetaFour t :=
  analyticOnNhd_of_diff (fun _ hs => differentiableAt_thetaFour hs) t ht

theorem analyticAt_E1 {t : ℂ} (ht : 0 < t.im) : AnalyticAt ℂ E1 t :=
  ((analyticAt_LB ht).sub (analyticAt_LA ht)).add (analyticAt_const.mul ((analyticAt_thetaFour ht).pow 4))
theorem analyticAt_E2 {t : ℂ} (ht : 0 < t.im) : AnalyticAt ℂ E2 t :=
  ((analyticAt_LB ht).sub (analyticAt_LC ht)).sub (analyticAt_const.mul ((analyticAt_thetaTwo ht).pow 4))
theorem analyticAt_E3 {t : ℂ} (ht : 0 < t.im) : AnalyticAt ℂ E3 t :=
  ((analyticAt_LA ht).sub (analyticAt_LC ht)).sub (analyticAt_const.mul ((analyticAt_thetaThree ht).pow 4))

theorem analyticAt_Psym {t : ℂ} (ht : 0 < t.im) : AnalyticAt ℂ Psym t :=
  (((analyticAt_E1 ht).pow 2).add ((analyticAt_E2 ht).pow 2)).add ((analyticAt_E3 ht).pow 2)
theorem analyticAt_Rsym {t : ℂ} (ht : 0 < t.im) : AnalyticAt ℂ Rsym t :=
  ((((analyticAt_E1 ht).pow 2).mul ((analyticAt_E2 ht).pow 2)).add
    (((analyticAt_E2 ht).pow 2).mul ((analyticAt_E3 ht).pow 2))).add
    (((analyticAt_E3 ht).pow 2).mul ((analyticAt_E1 ht).pow 2))

/-! ## J6. Behaviour at `i∞` -/

/-- The filter `Im t → ∞` on `ℂ`. -/
abbrev imInf : Filter ℂ := Filter.comap Complex.im Filter.atTop

theorem eventually_im_pos : ∀ᶠ t in imInf, 0 < t.im :=
  Filter.eventually_comap.mpr ((Filter.eventually_gt_atTop 0).mono fun _ h _ hx => hx ▸ h)

theorem tendsto_exp_neg_im : Tendsto (fun t : ℂ => Real.exp (-π * t.im)) imInf (𝓝 0) := by
  have : Tendsto (fun y : ℝ => Real.exp (-π * y)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact Filter.tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos] : -π < 0)
  exact this.comp Filter.tendsto_comap

theorem tendsto_thetaThree : Tendsto thetaThree imInf (𝓝 1) := by
  have h := isBigO_at_im_infty_jacobiTheta_sub_one.trans_tendsto tendsto_exp_neg_im
  have h' : Tendsto (fun t => jacobiTheta t - 1 + 1) imInf (𝓝 (0 + 1)) := h.add_const 1
  simp only [sub_add_cancel, zero_add] at h'
  refine h'.congr fun t => ?_
  rw [jacobiTheta_eq_jacobiTheta₂]; rfl

theorem tendsto_add_one_imInf : Tendsto (fun t : ℂ => t + 1) imInf imInf := by
  refine Filter.tendsto_comap_iff.mpr ?_
  have : (Complex.im ∘ fun t : ℂ => t + 1) = Complex.im := by funext t; simp
  rw [this]; exact Filter.tendsto_comap

theorem tendsto_thetaFour : Tendsto thetaFour imInf (𝓝 1) := by
  have := tendsto_thetaThree.comp tendsto_add_one_imInf
  refine this.congr fun t => ?_
  simp [thetaThree_add_one]

/-- `‖u(t) − 2‖ ≤ 2r/(1 − r)`, `r = e^{−π Im t}`. -/
theorem norm_uTheta_sub_two_le {t : ℂ} (ht : 0 < t.im) :
    ‖uTheta t - 2‖ ≤ 2 * Real.exp (-π * t.im) / (1 - Real.exp (-π * t.im)) := by
  set r := Real.exp (-π * t.im) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  set f : ℤ → ℂ := fun n => jacobiTheta₂_term n (t / 2) t with hf
  have hs : HasSum f (uTheta t) := hasSum_jacobiTheta₂_term (t / 2) ht
  have hnorm : ∀ n : ℤ, ‖f n‖ = r ^ (n * (n + 1)).toNat := by
    intro n
    rw [hf, norm_jacobiTheta₂_term, hr, ← Real.exp_nat_mul]
    congr 1
    have hnn : 0 ≤ n * (n + 1) := by nlinarith [sq_nonneg n]
    have : ((n * (n + 1)).toNat : ℝ) = ((n * (n + 1) : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnn
    rw [this]
    simp only [Complex.div_ofNat_im]
    push_cast
    ring
  set h : ℤ → ℂ := fun n => (if n = 0 then 1 else 0) + (if n = -1 then 1 else 0) with hh
  have hhs : HasSum h 2 := by
    have := (hasSum_ite_eq (0 : ℤ) (1 : ℂ)).add (hasSum_ite_eq (-1 : ℤ) (1 : ℂ))
    rw [show (1 : ℂ) + 1 = 2 by norm_num] at this
    exact this
  have hg : HasSum (fun n => f n - h n) (uTheta t - 2) := hs.sub hhs
  set b : ℤ → ℝ := fun n => if n = 0 then 0 else r ^ n.natAbs with hb
  have hbs : HasSum b (r / (1 - r) + r / (1 - r)) := by
    refine HasSum.of_nat_of_neg_add_one ?_ ?_
    · have hg' := (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
      have e : r * (1 - r)⁻¹ = r / (1 - r) := by rw [div_eq_mul_inv]
      rw [e] at hg'
      refine (hasSum_nat_add_iff' (f := fun n : ℕ => b n) (g := r / (1 - r)) 1).mp ?_
      simp only [hb, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ↓reduceIte, sub_zero]
      refine hg'.congr_fun fun n => ?_
      simp only [Nat.cast_add, Nat.cast_one]
      rw [if_neg (by omega)]
      have : ((n : ℤ) + 1).natAbs = n + 1 := by omega
      rw [this, pow_succ, mul_comm]
    · have hg' := (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
      have e : r * (1 - r)⁻¹ = r / (1 - r) := by rw [div_eq_mul_inv]
      rw [e] at hg'
      refine hg'.congr_fun fun n => ?_
      simp only [hb]
      rw [if_neg (by omega)]
      have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [this, pow_succ, mul_comm]
  have hbound : ∀ n : ℤ, ‖f n - h n‖ ≤ b n := by
    intro n
    by_cases h0 : n = 0
    · subst h0; simp [hh, hb, hf, jacobiTheta₂_term]
    by_cases h1 : n = -1
    · subst h1
      have : f (-1) = 1 := by
        simp only [hf, jacobiTheta₂_term]
        rw [← Complex.exp_zero]; congr 1; push_cast; ring
      simp [hh, hb, this, hr0]
    · have hhn : h n = 0 := by simp [hh, h0, h1]
      rw [hhn, sub_zero, hnorm]
      show r ^ _ ≤ if n = 0 then 0 else r ^ n.natAbs
      rw [if_neg h0]
      apply pow_le_pow_of_le_one hr0 hr1.le
      have : (n.natAbs : ℤ) ≤ n * (n + 1) := by
        rcases le_or_gt 0 n with hn | hn
        · rw [Int.natAbs_of_nonneg hn]; nlinarith [show 1 ≤ n by omega]
        · rw [Int.ofNat_natAbs_of_nonpos hn.le]; nlinarith [show n ≤ -2 by omega]
      omega
  have := hg.norm_le_of_bounded hbs hbound
  calc ‖uTheta t - 2‖ ≤ r / (1 - r) + r / (1 - r) := this
    _ = 2 * r / (1 - r) := by ring

theorem tendsto_uTheta : Tendsto uTheta imInf (𝓝 2) := by
  have hr : Tendsto (fun t : ℂ => 2 * Real.exp (-π * t.im) / (1 - Real.exp (-π * t.im))) imInf
      (𝓝 (2 * 0 / (1 - 0))) :=
    (tendsto_exp_neg_im.const_mul 2).div (tendsto_const_nhds.sub tendsto_exp_neg_im) (by norm_num)
  rw [show (2 : ℝ) * 0 / (1 - 0) = 0 by norm_num] at hr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hr
  filter_upwards [eventually_im_pos] with t ht
  exact norm_uTheta_sub_two_le ht

/-- **Cauchy estimate at `i∞`**: if `g → c` as `Im t → ∞` then `g' → 0`. -/
theorem tendsto_deriv_zero {g : ℂ → ℂ} {c : ℂ} (hd : ∀ t : ℂ, 0 < t.im → DifferentiableAt ℂ g t)
    (hg : Tendsto g imInf (𝓝 c)) : Tendsto (deriv g) imInf (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1 := Metric.tendsto_nhds.mp hg (ε / 4) (by positivity)
  have hA' : ∃ A : ℝ, ∀ s : ℂ, A ≤ s.im → dist (g s) c < ε / 4 := by
    have h1' := Filter.eventually_comap.mp h1
    rw [Filter.eventually_atTop] at h1'
    obtain ⟨A, hA⟩ := h1'
    exact ⟨A, fun s hs => hA s.im hs s rfl⟩
  obtain ⟨A, hA⟩ := hA'
  have h2 : ∀ᶠ t in imInf, max A 1 + 1 ≤ t.im :=
    Filter.eventually_comap.mpr ((Filter.eventually_ge_atTop (max A 1 + 1)).mono
      fun _ h _ hx => hx ▸ h)
  filter_upwards [h2] with t ht
  rw [dist_zero_right]
  have hsub : Metric.closedBall t (1 / 2) ⊆ {w : ℂ | 0 < w.im} := by
    intro s hs
    have := Complex.abs_im_le_norm (s - t)
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    simp only [Complex.sub_im] at this
    show 0 < s.im
    have := abs_le.mp (this.trans hs)
    linarith [le_max_right A 1]
  have hdc : DiffContOnCl ℂ (fun s => g s - c) (Metric.ball t (1 / 2)) :=
    DifferentiableOn.diffContOnCl_ball (U := {w : ℂ | 0 < w.im})
      (fun s hs => ((hd s hs).sub_const c).differentiableWithinAt) hsub
  have hC : ∀ s ∈ Metric.sphere t (1 / 2), ‖g s - c‖ ≤ ε / 4 := by
    intro s hs
    have hsi : A ≤ s.im := by
      have := Complex.abs_im_le_norm (s - t)
      rw [mem_sphere_iff_norm] at hs
      simp only [Complex.sub_im] at this
      have := abs_le.mp (this.trans hs.le)
      linarith [le_max_left A 1]
    have := hA s hsi
    rw [dist_eq_norm] at this
    exact this.le
  have hcd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hdc hC
  have hdd : deriv (fun s => g s - c) t = deriv g t := by
    rw [deriv_sub_const]
  rw [hdd] at hcd
  calc ‖deriv g t‖ ≤ ε / 4 / (1 / 2) := hcd
    _ < ε := by linarith


theorem tendsto_LB : Tendsto LB imInf (𝓝 0) := by
  have h := (tendsto_deriv_zero (fun t ht => differentiableAt_thetaThree ht) tendsto_thetaThree).div
    tendsto_thetaThree one_ne_zero
  rw [zero_div] at h
  exact h

theorem tendsto_LC : Tendsto LC imInf (𝓝 0) := by
  have h := (tendsto_deriv_zero (fun t ht => differentiableAt_thetaFour ht) tendsto_thetaFour).div
    tendsto_thetaFour one_ne_zero
  rw [zero_div] at h
  exact h

theorem LA_eq {t : ℂ} (ht : 0 < t.im) : LA t = π * I / 4 + deriv uTheta t / uTheta t := by
  have hu := differentiableAt_uTheta ht
  have he : HasDerivAt (fun s : ℂ => cexp (π * I * s / 4)) (π * I / 4 * cexp (π * I * t / 4)) t := by
    have h1 : HasDerivAt (fun s : ℂ => π * I * s / 4) (π * I / 4) t := by
      simpa using ((hasDerivAt_id t).const_mul (π * I : ℂ)).div_const 4
    have := h1.cexp
    convert this using 1; ring
  have hd : HasDerivAt thetaTwo (π * I / 4 * cexp (π * I * t / 4) * uTheta t +
      cexp (π * I * t / 4) * deriv uTheta t) t := he.mul hu.hasDerivAt
  have h2 := thetaTwo_ne_zero ht
  rw [thetaTwo_eq] at h2
  have hc : cexp (π * I * t / 4) ≠ 0 := Complex.exp_ne_zero _
  have hu0 : uTheta t ≠ 0 := fun h0 => h2 (by rw [h0, mul_zero])
  rw [LA, hd.deriv, thetaTwo_eq]
  field_simp

theorem tendsto_LA : Tendsto LA imInf (𝓝 (π * I / 4)) := by
  have h := (tendsto_deriv_zero (fun t ht => differentiableAt_uTheta ht) tendsto_uTheta).div
    tendsto_uTheta two_ne_zero
  rw [zero_div] at h
  have h' := h.const_add (π * I / 4)
  rw [add_zero] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_im_pos] with t ht
  exact (LA_eq ht).symm

theorem tendsto_cexp_pi_I : Tendsto (fun t : ℂ => cexp (π * I * t)) imInf (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_exp_neg_im.congr fun t => ?_
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem tendsto_thetaTwo_pow4 : Tendsto (fun t => thetaTwo t ^ 4) imInf (𝓝 0) := by
  have h := tendsto_cexp_pi_I.mul (tendsto_uTheta.pow 4)
  rw [zero_mul] at h
  refine h.congr fun t => ?_
  rw [thetaTwo_eq, mul_pow, ← Complex.exp_nat_mul]
  congr 2
  push_cast; ring

theorem tendsto_E1 : Tendsto E1 imInf (𝓝 0) := by
  have h := (tendsto_LB.sub tendsto_LA).add ((tendsto_const_nhds (x := π * I / 4)).mul (tendsto_thetaFour.pow 4))
  simp only [one_pow, mul_one, zero_sub, neg_add_cancel] at h
  exact h

theorem tendsto_E2 : Tendsto E2 imInf (𝓝 0) := by
  have h := (tendsto_LB.sub tendsto_LC).sub ((tendsto_const_nhds (x := π * I / 4)).mul tendsto_thetaTwo_pow4)
  simp only [sub_zero, mul_zero] at h
  exact h

theorem tendsto_E3 : Tendsto E3 imInf (𝓝 0) := by
  have h := (tendsto_LA.sub tendsto_LC).sub ((tendsto_const_nhds (x := π * I / 4)).mul (tendsto_thetaThree.pow 4))
  simp only [one_pow, mul_one, sub_zero, sub_self] at h
  exact h

theorem tendsto_Psym : Tendsto Psym imInf (𝓝 0) := by
  have h := ((tendsto_E1.pow 2).add (tendsto_E2.pow 2)).add (tendsto_E3.pow 2)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
  exact h

theorem tendsto_Rsym : Tendsto Rsym imInf (𝓝 0) := by
  have h := ((((tendsto_E1.pow 2).mul (tendsto_E2.pow 2))).add
    ((tendsto_E2.pow 2).mul (tendsto_E3.pow 2))).add ((tendsto_E3.pow 2).mul (tendsto_E1.pow 2))
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h
  exact h

theorem tendsto_coe_imInf : Tendsto (fun τ : UpperHalfPlane => (τ : ℂ)) UpperHalfPlane.atImInfty imInf := by
  refine Filter.tendsto_comap_iff.mpr ?_
  exact Filter.tendsto_comap


/-! ## J7. `P` and `R` are level-one cusp forms of weights 4 and 8, hence zero -/

section CuspForms

open UpperHalfPlane SlashInvariantForm

theorem slashP : ∀ γ : SL(2, ℤ), (fun τ : UpperHalfPlane => Psym τ) ∣[(4 : ℤ)] γ =
    fun τ : UpperHalfPlane => Psym τ := by
  intro γ
  have := slash_invariant_of_S_T (F := Psym) (k := 4) (fun _ ht => Psym_S ht) Psym_T γ
  exact_mod_cast this

theorem slashR : ∀ γ : SL(2, ℤ), (fun τ : UpperHalfPlane => Rsym τ) ∣[(8 : ℤ)] γ =
    fun τ : UpperHalfPlane => Rsym τ := by
  intro γ
  have := slash_invariant_of_S_T (F := Rsym) (k := 8) (fun _ ht => Rsym_S ht) Rsym_T γ
  exact_mod_cast this

theorem isZeroAtImInfty_P : IsZeroAtImInfty (fun τ : UpperHalfPlane => Psym τ) :=
  tendsto_Psym.comp tendsto_coe_imInf

theorem isZeroAtImInfty_R : IsZeroAtImInfty (fun τ : UpperHalfPlane => Rsym τ) :=
  tendsto_Rsym.comp tendsto_coe_imInf

/-- `P = E₁² + E₂² + E₃²` as a level-one cusp form of weight 4. -/
def PForm : CuspForm 𝒮ℒ 4 where
  toFun τ := Psym τ
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slashP A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine .congr (fun z hz => (analyticAt_Psym hz).differentiableAt.differentiableWithinAt)
      fun z hz => ?_
    simp [ofComplex_apply_of_im_pos hz]
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slashP γ]
    exact isZeroAtImInfty_P

/-- `R = E₁²E₂² + E₂²E₃² + E₃²E₁²` as a level-one cusp form of weight 8. -/
def RForm : CuspForm 𝒮ℒ 8 where
  toFun τ := Rsym τ
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slashR A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine .congr (fun z hz => (analyticAt_Rsym hz).differentiableAt.differentiableWithinAt)
      fun z hz => ?_
    simp [ofComplex_apply_of_im_pos hz]
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slashR γ]
    exact isZeroAtImInfty_R

theorem Psym_eq_zero {t : ℂ} (ht : 0 < t.im) : Psym t = 0 := by
  have h := rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve
    (k := 4) (by norm_num)) PForm
  have := congrArg (fun F : CuspForm 𝒮ℒ 4 => F ⟨t, ht⟩) h
  simp only [CuspForm.zero_apply] at this
  exact this

theorem Rsym_eq_zero {t : ℂ} (ht : 0 < t.im) : Rsym t = 0 := by
  have h := rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve
    (k := 8) (by norm_num)) RForm
  have := congrArg (fun F : CuspForm 𝒮ℒ 8 => F ⟨t, ht⟩) h
  simp only [CuspForm.zero_apply] at this
  exact this

end CuspForms


/-! ## J8. `E₁ = E₂ = E₃ = 0`, hence Jacobi's derivative formula -/

/-- If `f g = 0` on `ℍ` for analytic `f, g`, then `f = 0` or `g = 0` on `ℍ`. -/
theorem eq_zero_or_eq_zero_of_mul {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {w : ℂ | 0 < w.im}) (hg : AnalyticOnNhd ℂ g {w : ℂ | 0 < w.im})
    (hfg : ∀ t : ℂ, 0 < t.im → f t * g t = 0) :
    (∀ t : ℂ, 0 < t.im → f t = 0) ∨ (∀ t : ℂ, 0 < t.im → g t = 0) := by
  have hU : IsPreconnected {w : ℂ | 0 < w.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hI : (0 : ℝ) < (I : ℂ).im := by simp
  rcases (hf I hI).eventually_eq_zero_or_eventually_ne_zero with h | h
  · left
    intro t ht
    exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hI h ht
  · right
    have hg0 : ∀ᶠ z in 𝓝 I, g z = 0 := by
      rw [← (hg I hI).frequently_zero_iff_eventually_zero]
      have hpos : ∀ᶠ z in 𝓝[≠] I, 0 < z.im := nhdsWithin_le_nhds (U_isOpen.mem_nhds hI)
      refine ((h.and hpos).mono fun z hz => ?_).frequently
      exact (mul_eq_zero.mp (hfg z hz.2)).resolve_left hz.1
    intro t ht
    exact hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hI hg0 ht

/-- A primitive cube root of unity. -/
def omega3 : ℂ := (-1 + Real.sqrt 3 * I) / 2

theorem omega3_sq_add : omega3 ^ 2 + omega3 + 1 = 0 := by
  have h3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  simp only [omega3]
  ring_nf
  rw [Complex.I_sq, h3]
  ring

theorem omega3_ne_one : omega3 ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp [omega3] at this

theorem omega3_sq_ne_one : omega3 ^ 2 ≠ 1 := by
  intro h
  have h2 := omega3_sq_add
  rw [h] at h2
  have : omega3 = -2 := by linear_combination h2
  have := congrArg Complex.re this
  simp [omega3] at this
  norm_num at this

theorem E_eq_zero {t : ℂ} (ht : 0 < t.im) : E1 t = 0 := by
  -- `a = E₁², b = E₂²`: `a² + ab + b² = 0` on `ℍ`
  have hab : ∀ s : ℂ, 0 < s.im →
      (E1 s ^ 2 - omega3 * E2 s ^ 2) * (E1 s ^ 2 - omega3 ^ 2 * E2 s ^ 2) = 0 := by
    intro s hs
    have hP := Psym_eq_zero hs
    have hR := Rsym_eq_zero hs
    simp only [Psym, Rsym] at hP hR
    have hc : E3 s ^ 2 = -(E1 s ^ 2) - E2 s ^ 2 := by linear_combination hP
    rw [hc] at hR
    have hw := omega3_sq_add
    linear_combination (-1 : ℂ) * hR + (-(E1 s ^ 2 * E2 s ^ 2) + (omega3 - 1) * E2 s ^ 4) * hw
  have ha1 : AnalyticOnNhd ℂ (fun s => E1 s ^ 2 - omega3 * E2 s ^ 2) {w : ℂ | 0 < w.im} :=
    fun s hs => ((analyticAt_E1 hs).pow 2).sub (analyticAt_const.mul ((analyticAt_E2 hs).pow 2))
  have ha2 : AnalyticOnNhd ℂ (fun s => E1 s ^ 2 - omega3 ^ 2 * E2 s ^ 2) {w : ℂ | 0 < w.im} :=
    fun s hs => ((analyticAt_E1 hs).pow 2).sub (analyticAt_const.mul ((analyticAt_E2 hs).pow 2))
  have ht' := im_neg_inv_pos ht
  have hτ := ne_zero_of_im_pos ht
  have ht4 : t ^ 4 ≠ 0 := pow_ne_zero 4 hτ
  rcases eq_zero_or_eq_zero_of_mul ha1 ha2 hab with h | h
  · -- `E₁² = ω E₂²` on `ℍ`; at `−1/t`: `E₂² = ω E₁²`
    have h1 := h t ht
    have h2 := h (-1 / t) ht'
    rw [E1_S ht, E2_S ht] at h2
    have h2' : E2 t ^ 2 = omega3 * E1 t ^ 2 := by
      apply mul_left_cancel₀ ht4
      linear_combination h2
    have hb : (1 - omega3 ^ 2) * E2 t ^ 2 = 0 := by linear_combination h2' + omega3 * h1
    have hb0 : E2 t ^ 2 = 0 :=
      (mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr omega3_sq_ne_one.symm)
    have : E1 t ^ 2 = 0 := by linear_combination h1 + omega3 * hb0
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  · have h1 := h t ht
    have h2 := h (-1 / t) ht'
    rw [E1_S ht, E2_S ht] at h2
    have h2' : E2 t ^ 2 = omega3 ^ 2 * E1 t ^ 2 := by
      apply mul_left_cancel₀ ht4
      linear_combination h2
    have hw := omega3_sq_add
    -- `E₂² = ω⁴ E₂² = ω E₂²`
    have hw3 : omega3 ^ 3 = 1 := by linear_combination (omega3 - 1) * hw
    have hb : (1 - omega3) * E2 t ^ 2 = 0 := by
      linear_combination h2' + omega3 ^ 2 * h1 + omega3 * E2 t ^ 2 * hw3
    have hb0 : E2 t ^ 2 = 0 :=
      (mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr omega3_ne_one.symm)
    have : E1 t ^ 2 = 0 := by linear_combination h1 + omega3 ^ 2 * hb0
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this

/-- **Jacobi's derivative formula, proved**: `dλ/dt = πi λ θ₄⁴` for `λ = θ₂⁴/θ₃⁴`. -/
theorem jacobiLambdaDeriv : JacobiLambdaDeriv := by
  intro t ht
  have h2 := thetaTwo_ne_zero ht
  have h3 := thetaThree_ne_zero ht
  have hd := ((differentiableAt_thetaTwo ht).hasDerivAt.pow 4).div
    ((differentiableAt_thetaThree ht).hasDerivAt.pow 4) (pow_ne_zero 4 h3)
  have key : (fun s => thetaTwo s ^ 4 / thetaThree s ^ 4) = thetaTwo ^ 4 / thetaThree ^ 4 := by
    funext s; simp
  rw [key]
  convert hd using 1
  have hE := E_eq_zero ht
  simp only [E1, LB, LA] at hE
  have hq : deriv thetaTwo t / thetaTwo t =
      deriv thetaThree t / thetaThree t + π * I / 4 * thetaFour t ^ 4 := by
    linear_combination -hE
  rw [div_eq_iff h2] at hq
  simp only [Pi.pow_apply]
  rw [hq]
  norm_num
  field_simp
  ring

end ZInQ.GZWeil

#print axioms ZInQ.GZWeil.jacobiLambdaDeriv
