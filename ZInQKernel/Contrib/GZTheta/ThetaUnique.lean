import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# gz-theta: uniqueness of the theta function of level one

Fix `τ` with `Im τ > 0`. An entire function `f` with `f(z + 1) = f(z)` and
`f(z + τ) = e^{−π i (τ + 2z)} f(z)` (the functional equations of Jacobi's `θ(z, τ)`) and with
`∫₀¹ f = 0` vanishes identically.

Proof: the Fourier coefficients `a_n = ∫₀¹ f(x) e^{−2π i n x} dx` satisfy
`a_n = e^{−π i τ (2n+1)} a_{n+1}` (Cauchy's theorem on rectangles moves the segment `[0, 1]` to
`[τ, τ + 1]`), so `a₀ = 0` forces all `a_n = 0`; then `f = 0` on `ℝ` (Fourier series of a
continuous periodic function, Mathlib `has_pointwise_sum_fourier_series_of_summable`), and
`f = 0` by the identity theorem.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real

noncomputable section

namespace ZInQ.GZTheta

variable {τ : ℂ} {f : ℂ → ℂ}

/-- `g_n(z) = f(z) e^{−2π i n z}`. -/
def fourierTwist (f : ℂ → ℂ) (n : ℤ) (z : ℂ) : ℂ := f z * cexp (-2 * π * I * n * z)

theorem fourierTwist_add_one (h1 : ∀ z, f (z + 1) = f z) (n : ℤ) (z : ℂ) :
    fourierTwist f n (z + 1) = fourierTwist f n z := by
  unfold fourierTwist
  rw [h1]
  congr 1
  have : -2 * π * I * n * (z + 1) = -2 * π * I * n * z + (-n : ℤ) * (2 * π * I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem differentiable_fourierTwist (hf : Differentiable ℂ f) (n : ℤ) :
    Differentiable ℂ (fourierTwist f n) := by
  unfold fourierTwist
  fun_prop

/-- Moving the horizontal segment up by `y`. -/
theorem integral_fourierTwist_add_mul_I (hf : Differentiable ℂ f) (h1 : ∀ z, f (z + 1) = f z)
    (n : ℤ) (y : ℝ) :
    ∫ x : ℝ in (0 : ℝ)..1, fourierTwist f n (x + y * I) =
      ∫ x : ℝ in (0 : ℝ)..1, fourierTwist f n x := by
  have H := integral_boundary_rect_eq_zero_of_differentiableOn (fourierTwist f n) 0 (1 + y * I)
    ((differentiable_fourierTwist hf n).differentiableOn)
  simp only [zero_re, add_re, one_re, mul_re, I_re, mul_zero, ofReal_re, I_im, mul_one,
    sub_self, add_zero, zero_im, add_im, one_im, mul_im, ofReal_im, zero_add, ofReal_zero,
    zero_mul] at H
  have hv : (∫ t : ℝ in (0 : ℝ)..y, fourierTwist f n (1 + t * I)) =
      ∫ t : ℝ in (0 : ℝ)..y, fourierTwist f n (t * I) := by
    congr 1
    ext t
    rw [add_comm, fourierTwist_add_one h1]
  simp only [ofReal_one] at H
  rw [hv] at H
  have : (∫ x : ℝ in (0 : ℝ)..1, fourierTwist f n x) -
      ∫ x : ℝ in (0 : ℝ)..1, fourierTwist f n (x + y * I) = 0 := by
    have H' := H
    simp only [smul_eq_mul] at H'
    linear_combination H'
  linear_combination -this

/-- Shifting the segment horizontally by `s`. -/
theorem integral_fourierTwist_add_real (h1 : ∀ z, f (z + 1) = f z) (n : ℤ) (s : ℝ) (w : ℂ) :
    ∫ x : ℝ in (0 : ℝ)..1, fourierTwist f n (x + s + w) =
      ∫ x : ℝ in (0 : ℝ)..1, fourierTwist f n (x + w) := by
  have hper : Function.Periodic (fun x : ℝ => fourierTwist f n (x + w)) 1 := by
    intro x
    simp only [ofReal_add, ofReal_one]
    rw [show (x : ℂ) + 1 + w = (x + w) + 1 by ring, fourierTwist_add_one h1]
  have := hper.intervalIntegral_add_eq s 0
  rw [zero_add, add_comm s 1] at this
  have e : (∫ x : ℝ in (0 : ℝ)..1, fourierTwist f n (x + s + w)) =
      ∫ x : ℝ in (0 : ℝ)..1, (fun x : ℝ => fourierTwist f n (x + w)) (x + s) := by
    congr 1
    ext x
    simp only [ofReal_add]
  have hc := intervalIntegral.integral_comp_add_right (a := 0) (b := 1)
    (fun x : ℝ => fourierTwist f n (x + w)) s
  rw [e, hc, zero_add, this]


theorem fourierTwist_add_tau (hτ : ∀ z, f (z + τ) = cexp (-π * I * (τ + 2 * z)) * f z)
    (n : ℤ) (z : ℂ) :
    fourierTwist f n (z + τ) = cexp (-π * I * τ * (2 * n + 1)) * fourierTwist f (n + 1) z := by
  unfold fourierTwist
  rw [hτ]
  have : cexp (-π * I * (τ + 2 * z)) * cexp (-2 * π * I * n * (z + τ)) =
      cexp (-π * I * τ * (2 * n + 1)) * cexp (-2 * π * I * ((n + 1 : ℤ) : ℂ) * z) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (f z) * this

/-- The recursion of the Fourier coefficients. -/
theorem integral_fourierTwist_succ (hf : Differentiable ℂ f) (h1 : ∀ z, f (z + 1) = f z)
    (hτ : ∀ z, f (z + τ) = cexp (-π * I * (τ + 2 * z)) * f z) (n : ℤ) :
    ∫ x : ℝ in (0 : ℝ)..1, fourierTwist f n x =
      cexp (-π * I * τ * (2 * n + 1)) * ∫ x : ℝ in (0 : ℝ)..1, fourierTwist f (n + 1) x := by
  have e1 := integral_fourierTwist_add_real h1 n τ.re (τ.im * I)
  rw [integral_fourierTwist_add_mul_I hf h1] at e1
  rw [← e1, ← intervalIntegral.integral_const_mul]
  congr 1
  ext x
  rw [add_assoc, Complex.re_add_im, fourierTwist_add_tau hτ]

theorem integral_fourierTwist_eq_zero (hf : Differentiable ℂ f) (h1 : ∀ z, f (z + 1) = f z)
    (hτ : ∀ z, f (z + τ) = cexp (-π * I * (τ + 2 * z)) * f z)
    (h0 : ∫ x : ℝ in (0 : ℝ)..1, f x = 0) (n : ℤ) :
    ∫ x : ℝ in (0 : ℝ)..1, fourierTwist f n x = 0 := by
  have hκ : ∀ m : ℤ, cexp (-π * I * τ * (2 * m + 1)) ≠ 0 := fun _ => Complex.exp_ne_zero _
  induction n using Int.induction_on with
  | zero =>
    have : (fun x : ℝ => fourierTwist f 0 x) = fun x : ℝ => f x := by
      ext x; simp [fourierTwist]
    rw [this]; exact h0
  | succ k ih =>
    have := integral_fourierTwist_succ hf h1 hτ k
    rw [ih] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (hκ k)
  | pred k ih =>
    have := integral_fourierTwist_succ hf h1 hτ (-(k : ℤ) - 1)
    rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring, ih, mul_zero] at this
    exact this

/-- **Uniqueness of the level-one theta function.** -/
theorem eq_zero_of_theta_fe (hf : Differentiable ℂ f)
    (h1 : ∀ z, f (z + 1) = f z) (hτ : ∀ z, f (z + τ) = cexp (-π * I * (τ + 2 * z)) * f z)
    (h0 : ∫ x : ℝ in (0 : ℝ)..1, f x = 0) : f = 0 := by
  have hT : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  -- the restriction to `ℝ` as a continuous function on the circle
  let F : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨AddCircle.liftIco 1 0 (fun x : ℝ => f x),
      AddCircle.liftIco_continuous (by simpa using (h1 0).symm)
        (hf.continuous.comp continuous_ofReal).continuousOn⟩
  have hcoeff : ∀ n : ℤ, fourierCoeff F n = 0 := by
    intro n
    have e := fourierCoeff_liftIco_eq (T := 1) (a := 0) (fun x : ℝ => f x) n
    change fourierCoeff (AddCircle.liftIco 1 0 (fun x : ℝ => f x)) n = 0
    rw [e, fourierCoeffOn_eq_integral]
    have hz := integral_fourierTwist_eq_zero hf h1 hτ h0 n
    simp only [zero_add, sub_zero, div_one, one_smul]
    rw [← hz]
    congr 1
    ext x
    rw [fourier_coe_apply, smul_eq_mul, fourierTwist, mul_comm]
    congr 2
    push_cast
    ring
  have hzero : ∀ x : AddCircle (1 : ℝ), F x = 0 := by
    intro x
    have hs : Summable (fourierCoeff F) := by
      rw [show fourierCoeff F = 0 from funext hcoeff]; exact summable_zero
    have := has_pointwise_sum_fourier_series_of_summable hs x
    simp only [hcoeff, zero_smul] at this
    exact this.unique hasSum_zero
  have hreal : ∀ x : ℝ, x ∈ Set.Ico (0 : ℝ) 1 → f x = 0 := by
    intro x hx
    have := hzero x
    change AddCircle.liftIco 1 0 (fun x : ℝ => f x) x = 0 at this
    rw [AddCircle.liftIco_coe_apply (by simpa using hx)] at this
    exact this
  -- identity theorem
  have han : AnalyticOnNhd ℂ f Set.univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hfreq : ∃ᶠ z in nhdsWithin (1 / 2 : ℂ) {(1 / 2 : ℂ)}ᶜ, f z = 0 := by
    have hev : ∀ᶠ x : ℝ in nhdsWithin (1 / 2 : ℝ) {(1 / 2 : ℝ)}ᶜ, f (x : ℂ) = 0 := by
      have : Set.Ioo (0 : ℝ) 1 ∈ nhds (1 / 2 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
      filter_upwards [nhdsWithin_le_nhds this] with x hx
      exact hreal x ⟨hx.1.le, hx.2⟩
    have ht : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (nhdsWithin (1 / 2 : ℝ) {(1 / 2 : ℝ)}ᶜ)
        (nhdsWithin (1 / 2 : ℂ) {(1 / 2 : ℂ)}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h := continuous_ofReal.tendsto (1 / 2 : ℝ)
        rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; ring] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        intro h
        apply hx
        have h' : (x : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; exact h
        exact_mod_cast h'
    exact ht.frequently hev.frequently
  ext z
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ _) hfreq (Set.mem_univ z)

end ZInQ.GZTheta
