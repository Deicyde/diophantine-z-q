import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilTheta
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Liouville

/-!
# jacobi-lambda: Jacobi's derivative formula `dλ/dt = πi λ θ₄⁴`, proved

Task jacobi-lambda (2026-11-15). Report: `docs/research/jacobi-lambda.md`; scratch and log:
`scratch/jacobi-lambda/`.

This file proves gz-weil's printed leaf `ZInQ.GZWeil.JacobiLambdaDeriv` (`WeilTheta.lean`) outright,
from Mathlib's `jacobiTheta₂` alone (plus one bound from gz-theta's `TripleProduct.lean`), so gz-weil's
`ShimuraCMParamCd`, `X0.EtaModelDifferential` and `ModularParamC1` become unconditional theorems.

Proof (all elementary; no modular forms, no products):

1. **Duplication formula** (`jacobiTheta₂_mul_jacobiTheta₂`), by reindexing the double series along
   `(a, b) ↦ (a + b, a − b)` and `(a, b) ↦ (a + b + 1, a − b)`:
   `θ(z,τ)θ(w,τ) = θ(z+w,2τ)θ(z−w,2τ) + e^{2πiz+πiτ} θ(z+w+τ,2τ)θ(z−w+τ,2τ)`.
2. **Landen's identities** (`landen_three`, `landen_four`, `landen_two`, `landen_three_four`):
   `θ₃(τ)² = θ₃(2τ)² + θ₂(2τ)²`, `θ₄(τ)² = θ₃(2τ)² − θ₂(2τ)²`, `θ₂(τ)² = 2θ₂(2τ)θ₃(2τ)`,
   `θ₃(τ)θ₄(τ) = θ₄(2τ)²`, and **Jacobi's quartic** `θ₃⁴ = θ₂⁴ + θ₄⁴` (`jacobi_quartic`).
3. **Nonvanishing** of `θ₂, θ₃, θ₄` on `ℍ`: a zero at `τ` propagates to `2τ` by Landen, but the theta
   constants are close to their constant terms once `Im τ ≥ 1`.
4. **The Landen recursion**: with `h = θ₂/θ₃` and `F = h'/h − (πi/4)θ₄⁴`, differentiating
   `h(τ)²(1 + h(2τ)²) = 2h(2τ)` gives `F(τ) = (θ₄(τ)²/θ₃(τ)²) F(2τ)` (`Fq_rec`).
5. **Decay**: `‖F(σ)‖ ≤ C e^{−π Im σ}` for `Im σ ≥ 2` (Cauchy's estimate on the unit circle,
   `norm_Fq_le`); since `e^{−π Im 2σ} = (e^{−π Im σ})²`, the recursion halves the constant at each step
   for `Im σ ≥ 43`, so `F = 0` there, and then on all of `ℍ` by the recursion (`Fq_eq_zero`).
6. `λ = h⁴`, so `λ' = 4h³h' = πi λ θ₄⁴` (`jacobiLambdaDeriv`).

Main results: `ZInQ.GZWeil.jacobiLambdaDeriv : ZInQ.GZWeil.JacobiLambdaDeriv`,
`ZInQ.GZWeil.etaModelDifferential`, `ZInQ.GZWeil.modularParamC1`, `ZInQ.GZWeil.shimuraCMParamCd`,
`ZInQ.GZWeil.grossZagierHeegnerCd_of_leaves4`. No `sorry`, no `axiom`.
-/

open Complex Filter Topology Metric
open scoped Real

noncomputable section

namespace ZInQ.JacobiLambda

open ZInQ.GZWeil (thetaTwo thetaThree thetaFour)


lemma summable_norm_term (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => ‖jacobiTheta₂_term n z τ‖) :=
  (summable_pow_mul_jacobiTheta₂_term_bound |z.im| hτ 0).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by simpa using norm_jacobiTheta₂_term_le hτ (le_refl _) (le_refl _) n)

lemma hasSum_prod_term (z w : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun p : ℤ × ℤ => jacobiTheta₂_term p.1 z τ * jacobiTheta₂_term p.2 w τ)
      (jacobiTheta₂ z τ * jacobiTheta₂ w τ) := by
  have := summable_mul_of_summable_norm (summable_norm_term z hτ) (summable_norm_term w hτ)
  rw [jacobiTheta₂, jacobiTheta₂,
    tsum_mul_tsum_of_summable_norm (summable_norm_term z hτ) (summable_norm_term w hτ)]
  exact this.hasSum

/-- `(a, b) ↦ (a + b, a − b)` and `(a, b) ↦ (a + b + 1, a − b)`. -/
def dupMap : (ℤ × ℤ) ⊕ (ℤ × ℤ) → ℤ × ℤ
  | Sum.inl p => (p.1 + p.2, p.1 - p.2)
  | Sum.inr p => (p.1 + p.2 + 1, p.1 - p.2)

lemma dupMap_bijective : Function.Bijective dupMap := by
  constructor
  · rintro (⟨a, b⟩ | ⟨a, b⟩) (⟨c, d⟩ | ⟨c, d⟩) h <;>
      simp only [dupMap, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h ⊢ <;>
      omega
  · rintro ⟨n, m⟩
    rcases Int.even_or_odd (n + m) with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨Sum.inl (k, n - k), by simp only [dupMap, Prod.mk.injEq]; omega⟩
    · exact ⟨Sum.inr (k, n - k - 1), by simp only [dupMap, Prod.mk.injEq]; omega⟩

/-- **The duplication formula** for Mathlib's `jacobiTheta₂`:
`θ(z,τ) θ(w,τ) = θ(z+w,2τ) θ(z−w,2τ) + e^{2πiz+πiτ} θ(z+w+τ,2τ) θ(z−w+τ,2τ)`. -/
theorem jacobiTheta₂_mul_jacobiTheta₂ (z w : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ z τ * jacobiTheta₂ w τ =
      jacobiTheta₂ (z + w) (2 * τ) * jacobiTheta₂ (z - w) (2 * τ) +
      cexp (2 * π * I * z + π * I * τ) *
        (jacobiTheta₂ (z + w + τ) (2 * τ) * jacobiTheta₂ (z - w + τ) (2 * τ)) := by
  have h2 : 0 < (2 * τ).im := by simp; linarith
  set f : ℤ × ℤ → ℂ := fun p => jacobiTheta₂_term p.1 z τ * jacobiTheta₂_term p.2 w τ with hf_def
  have hf := hasSum_prod_term z w hτ
  have hA := hasSum_prod_term (z + w) (z - w) h2
  have hB := (hasSum_prod_term (z + w + τ) (z - w + τ) h2).mul_left (cexp (2 * π * I * z + π * I * τ))
  have hS : HasSum (f ∘ dupMap) _ := HasSum.sum (f := f ∘ dupMap) (a := _) (b := _)
    (by
      convert hA using 1
      funext p
      simp only [Function.comp, dupMap, hf_def, jacobiTheta₂_term, ← Complex.exp_add]
      congr 1; push_cast; ring)
    (by
      convert hB using 1
      funext p
      simp only [Function.comp, dupMap, hf_def, jacobiTheta₂_term, ← Complex.exp_add]
      congr 1; push_cast; ring)
  have e := Equiv.ofBijective dupMap dupMap_bijective
  rw [show (f ∘ dupMap) = f ∘ (Equiv.ofBijective dupMap dupMap_bijective) from rfl,
    Equiv.hasSum_iff] at hS
  exact hf.unique hS

/-! ## Landen's transformation and Jacobi's quartic identity -/

lemma thetaTwo_two_mul (τ : ℂ) :
    thetaTwo (2 * τ) = cexp (π * I * τ / 2) * jacobiTheta₂ τ (2 * τ) := by
  rw [thetaTwo, mul_div_cancel_left₀ _ two_ne_zero]
  congr 2; ring

lemma thetaTwo_two_mul_sq (τ : ℂ) :
    thetaTwo (2 * τ) ^ 2 = cexp (π * I * τ) * jacobiTheta₂ τ (2 * τ) ^ 2 := by
  rw [thetaTwo_two_mul, mul_pow, ← Complex.exp_nat_mul]
  congr 2; push_cast; ring

/-- `θ(τ + 1/2, 2τ) = 0`. -/
lemma jacobiTheta₂_add_half_two_mul (τ : ℂ) : jacobiTheta₂ (τ + 1 / 2) (2 * τ) = 0 := by
  have h1 : jacobiTheta₂ (τ - 1 / 2) (2 * τ) = jacobiTheta₂ (τ + 1 / 2) (2 * τ) := by
    rw [← jacobiTheta₂_add_left]; congr 1; ring
  have h2 := jacobiTheta₂_add_left' (-(τ + 1 / 2)) (2 * τ)
  rw [jacobiTheta₂_neg_left, show -(τ + 1 / 2) + 2 * τ = τ - 1 / 2 by ring, h1,
    show -π * I * (2 * τ + 2 * -(τ + 1 / 2)) = π * I by ring, Complex.exp_pi_mul_I] at h2
  linear_combination h2 / 2

theorem landen_three {τ : ℂ} (hτ : 0 < τ.im) :
    thetaThree τ ^ 2 = thetaThree (2 * τ) ^ 2 + thetaTwo (2 * τ) ^ 2 := by
  have h := jacobiTheta₂_mul_jacobiTheta₂ 0 0 hτ
  simp only [add_zero, sub_zero, zero_add, mul_zero] at h
  rw [thetaTwo_two_mul_sq, thetaThree, thetaThree, sq, h]
  ring_nf

theorem landen_four {τ : ℂ} (hτ : 0 < τ.im) :
    thetaFour τ ^ 2 = thetaThree (2 * τ) ^ 2 - thetaTwo (2 * τ) ^ 2 := by
  have h := jacobiTheta₂_mul_jacobiTheta₂ (1 / 2) (1 / 2) hτ
  rw [show (1 / 2 : ℂ) + 1 / 2 = 0 + 1 by norm_num, sub_self, jacobiTheta₂_add_left,
    show (0 : ℂ) + 1 + τ = τ + 1 by ring, jacobiTheta₂_add_left, zero_add,
    show 2 * π * I * (1 / 2) + π * I * τ = π * I + π * I * τ by ring, Complex.exp_add,
    Complex.exp_pi_mul_I] at h
  rw [thetaTwo_two_mul_sq, thetaThree, thetaFour, sq, h]
  ring

theorem landen_two {τ : ℂ} (hτ : 0 < τ.im) :
    thetaTwo τ ^ 2 = 2 * thetaTwo (2 * τ) * thetaThree (2 * τ) := by
  have h := jacobiTheta₂_mul_jacobiTheta₂ (τ / 2) (τ / 2) hτ
  have h2 := jacobiTheta₂_add_left' 0 (2 * τ)
  rw [zero_add] at h2
  rw [show τ / 2 + τ / 2 = τ by ring, sub_self, zero_add,
    show τ + τ = 2 * τ by ring, h2] at h
  rw [thetaTwo, thetaTwo_two_mul, thetaThree, mul_pow, sq (jacobiTheta₂ (τ / 2) τ), h]
  have e1 : cexp (π * I * τ / 4) ^ 2 = cexp (π * I * τ / 2) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : cexp (2 * π * I * (τ / 2) + π * I * τ) * cexp (-π * I * (2 * τ + 2 * 0)) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring
  rw [e1]
  linear_combination (cexp (π * I * τ / 2) * jacobiTheta₂ τ (2 * τ) * jacobiTheta₂ 0 (2 * τ)) * e2

theorem landen_three_four {τ : ℂ} (hτ : 0 < τ.im) :
    thetaThree τ * thetaFour τ = thetaFour (2 * τ) ^ 2 := by
  have h := jacobiTheta₂_mul_jacobiTheta₂ 0 (1 / 2) hτ
  rw [zero_add, zero_sub, jacobiTheta₂_neg_left, show (1 / 2 : ℂ) + τ = τ + 1 / 2 by ring,
    jacobiTheta₂_add_half_two_mul] at h
  rw [thetaThree, thetaFour, thetaFour, h]
  ring

/-- **Jacobi's quartic identity** `θ₃⁴ = θ₂⁴ + θ₄⁴`. -/
theorem jacobi_quartic {σ : ℂ} (hσ : 0 < σ.im) :
    thetaThree σ ^ 4 = thetaTwo σ ^ 4 + thetaFour σ ^ 4 := by
  have hτ : 0 < (σ / 2).im := by simp; linarith
  have e : 2 * (σ / 2) = σ := by ring
  have h3 := landen_three hτ
  have h4 := landen_four hτ
  have h34 := landen_three_four hτ
  rw [e] at h3 h4 h34
  have : thetaFour σ ^ 4 = (thetaThree (σ / 2) * thetaFour (σ / 2)) ^ 2 := by rw [h34]; ring
  rw [this, mul_pow, h3, h4]
  ring

/-! ## Exponential bounds near `i∞` -/

/-- `θ₂(s) = e^{πis/4} T(s)`, `T(s) = Σ e^{πi n(n+1) s}`. -/
def thT (s : ℂ) : ℂ := jacobiTheta₂ (s / 2) s

lemma thetaTwo_eq (s : ℂ) : thetaTwo s = cexp (π * I * s / 4) * thT s := rfl

lemma norm_le_of_hasSum_geom {g : ℕ → ℂ} {a : ℂ} (hg : HasSum g a) {C r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hb : ∀ n, ‖g n‖ ≤ C * r ^ (n + 1)) : ‖a‖ ≤ C * (r / (1 - r)) := by
  have s : HasSum (fun n : ℕ => C * r ^ (n + 1)) (C * (r / (1 - r))) := by
    have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (C * r)
    convert this using 1
    · funext n; ring
    · ring
  have aux : Summable fun n => ‖g n‖ := .of_nonneg_of_le (fun n => norm_nonneg _) hb s.summable
  rw [← hg.tsum_eq]
  exact (norm_tsum_le_tsum_norm aux).trans ((aux.tsum_mono s.summable hb).trans_eq s.tsum_eq)

lemma norm_cexp_pi_I_mul (m : ℝ) (s : ℂ) : ‖cexp (π * I * m * s)‖ = rexp (-π * m * s.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma hasSum_thT_sub_two {s : ℂ} (hs : 0 < s.im) :
    HasSum (fun n : ℕ => 2 * cexp (π * I * ((((n : ℝ) + 1) * ((n : ℝ) + 2) : ℝ) : ℂ) * s))
      (thT s - 2) := by
  have h0 := (hasSum_jacobiTheta₂_term (s / 2) hs).nat_add_neg_add_one
  have e : ∀ n : ℕ, jacobiTheta₂_term n (s / 2) s + jacobiTheta₂_term (-(n + 1)) (s / 2) s =
      2 * cexp (π * I * (((n : ℝ) * ((n : ℝ) + 1) : ℝ) : ℂ) * s) := by
    intro n
    simp only [jacobiTheta₂_term]
    have e1 : cexp (2 * π * I * ((-(n + 1) : ℤ) : ℂ) * (s / 2) + π * I * ((-(n + 1) : ℤ) : ℂ) ^ 2 * s)
        = cexp (π * I * (((n : ℝ) * ((n : ℝ) + 1) : ℝ) : ℂ) * s) := by
      congr 1; push_cast; ring
    have e2 : cexp (2 * π * I * ((n : ℤ) : ℂ) * (s / 2) + π * I * ((n : ℤ) : ℂ) ^ 2 * s)
        = cexp (π * I * (((n : ℝ) * ((n : ℝ) + 1) : ℝ) : ℂ) * s) := by
      congr 1; push_cast; ring
    rw [e1, e2]; ring
  have h1 : HasSum (fun n : ℕ => 2 * cexp (π * I * (((n : ℝ) * ((n : ℝ) + 1) : ℝ) : ℂ) * s))
      (thT s) := by
    convert h0 using 1
    · funext n
      exact (e n).symm
    · rfl
  rw [← hasSum_nat_add_iff' 1] at h1
  convert h1 using 1
  · funext n; push_cast; ring_nf
  · simp [thT]

lemma exp_neg_pi_le_quarter {t : ℝ} (ht : 1 ≤ t) : rexp (-π * t) ≤ 1 / 4 := by
  have h1 : rexp (-π * t) ≤ rexp (-π) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have h2 : 4 ≤ rexp π := by linarith [Real.add_one_le_exp π, Real.pi_gt_three]
  rw [Real.exp_neg] at h1
  calc rexp (-π * t) ≤ (rexp π)⁻¹ := h1
    _ ≤ 1 / 4 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2

lemma geom_aux {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 4) : 2 * (r / (1 - r)) ≤ 3 * r := by
  rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith

theorem norm_thT_sub_two_le {s : ℂ} (hs : 1 ≤ s.im) : ‖thT s - 2‖ ≤ 3 * rexp (-π * s.im) := by
  have hs0 : 0 < s.im := by linarith
  set r := rexp (-π * s.im) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hrq := exp_neg_pi_le_quarter hs
  refine (norm_le_of_hasSum_geom (hasSum_thT_sub_two hs0) hr0 (by linarith) (C := 2) ?_).trans
    (geom_aux hr0 hrq)
  intro n
  rw [norm_mul, norm_cexp_pi_I_mul, Complex.norm_two, hr, ← Real.exp_nat_mul]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  push_cast
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith [Real.pi_pos, mul_nonneg (mul_nonneg Real.pi_pos.le hs0.le) this]

theorem norm_thetaThree_sub_one_le {s : ℂ} (hs : 1 ≤ s.im) :
    ‖thetaThree s - 1‖ ≤ 3 * rexp (-π * s.im) := by
  have hs0 : 0 < s.im := by linarith
  have h := norm_jacobiTheta_sub_one_le hs0
  rw [jacobiTheta_eq_jacobiTheta₂] at h
  have hrq := exp_neg_pi_le_quarter hs
  have hr0 := (Real.exp_pos (-π * s.im)).le
  refine h.trans ?_
  have := geom_aux hr0 hrq
  have e : 2 / (1 - rexp (-π * s.im)) * rexp (-π * s.im) =
      2 * (rexp (-π * s.im) / (1 - rexp (-π * s.im))) := by ring
  linarith

theorem norm_thetaFour_sub_one_le {s : ℂ} (hs : 1 ≤ s.im) :
    ‖thetaFour s - 1‖ ≤ 3 * rexp (-π * s.im) := by
  have hs0 : 0 < s.im := by linarith
  have h := ZInQ.GZTheta.norm_jacobiTheta₂_half_sub_one_le hs0
  rw [ZInQ.GZTheta.norm_qJ] at h
  have hrq := exp_neg_pi_le_quarter hs
  have hr0 := (Real.exp_pos (-π * s.im)).le
  refine h.trans ?_
  have := geom_aux hr0 hrq
  have e : 2 / (1 - rexp (-π * s.im)) * rexp (-π * s.im) =
      2 * (rexp (-π * s.im) / (1 - rexp (-π * s.im))) := by ring
  linarith

/-! ## Differentiability and Cauchy estimates -/

lemma im_ge_of_mem_closedBall {σ z : ℂ} (hz : z ∈ closedBall σ 1) : σ.im - 1 ≤ z.im := by
  have h := Complex.abs_im_le_norm (z - σ)
  rw [mem_closedBall, dist_eq_norm] at hz
  rw [Complex.sub_im] at h
  have := (abs_le.mp (h.trans hz)).1
  linarith

lemma differentiableAt_thT {s : ℂ} (hs : 0 < s.im) : DifferentiableAt ℂ thT s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (s / 2, s)) s :=
    (differentiableAt_id.div_const 2).prodMk differentiableAt_id
  have h2 := (hasFDerivAt_jacobiTheta₂ (s / 2) hs).differentiableAt
  exact DifferentiableAt.comp (f := fun s : ℂ => (s / 2, s))
      (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) s h2 h1

lemma differentiableAt_thetaThree' {s : ℂ} (hs : 0 < s.im) :
    DifferentiableAt ℂ thetaThree s :=
  differentiableAt_jacobiTheta₂_snd 0 hs

lemma differentiableAt_thetaTwo' {s : ℂ} (hs : 0 < s.im) : DifferentiableAt ℂ thetaTwo s := by
  have h4 : DifferentiableAt ℂ (fun s : ℂ => cexp (π * I * s / 4)) s :=
    ((differentiableAt_id.const_mul (π * I : ℂ)).div_const 4).cexp
  exact h4.mul (differentiableAt_thT hs)

/-- Cauchy's estimate on the unit circle around `σ`, `Im σ ≥ 2`. -/
lemma norm_deriv_le_of_bound {f : ℂ → ℂ} {c : ℂ}
    (hf : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ f z)
    (hb : ∀ z : ℂ, 1 ≤ z.im → ‖f z - c‖ ≤ 3 * rexp (-π * z.im)) {σ : ℂ} (hσ : 2 ≤ σ.im) :
    ‖deriv f σ‖ ≤ 3 * rexp π * rexp (-π * σ.im) := by
  have hd : DiffContOnCl ℂ (fun z => f z - c) (ball σ 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball σ one_ne_zero]
    intro z hz
    have := im_ge_of_mem_closedBall hz
    exact ((hf z (by linarith)).sub_const c).differentiableWithinAt
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hd
    (C := 3 * rexp π * rexp (-π * σ.im)) (fun z hz => by
      have hz' := im_ge_of_mem_closedBall (sphere_subset_closedBall hz)
      refine (hb z (by linarith)).trans ?_
      rw [mul_assoc, ← Real.exp_add]
      gcongr
      nlinarith [Real.pi_pos])
  rw [deriv_sub_const, div_one] at h
  exact h

/-! ## Nonvanishing -/

lemma im_two_pow_mul (k : ℕ) (σ : ℂ) : ((2 : ℂ) ^ k * σ).im = 2 ^ k * σ.im := by
  have : (2 : ℂ) ^ k = ((2 ^ k : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.im_ofReal_mul]

lemma not_of_iterate {P : ℂ → Prop} (hstep : ∀ σ : ℂ, 0 < σ.im → P σ → P (2 * σ)) (y : ℝ)
    (hbig : ∀ σ : ℂ, y ≤ σ.im → ¬ P σ) {σ : ℂ} (hσ : 0 < σ.im) : ¬ P σ := by
  intro hP
  have key : ∀ k : ℕ, P ((2 : ℂ) ^ k * σ) := by
    intro k
    induction k with
    | zero => simpa using hP
    | succ k ih =>
      have hk : 0 < ((2 : ℂ) ^ k * σ).im := by rw [im_two_pow_mul]; positivity
      have := hstep _ hk ih
      rw [pow_succ, mul_comm ((2 : ℂ) ^ k) 2, mul_assoc]
      exact this
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (y / σ.im) (one_lt_two : (1 : ℝ) < 2)
  apply hbig _ _ (key k)
  rw [im_two_pow_mul]
  rw [div_lt_iff₀ hσ] at hk
  linarith

lemma two_mul_im_pos {s : ℂ} (hs : 0 < s.im) : 0 < (2 * s).im := by simp; linarith

theorem thetaFour_ne_zero {σ : ℂ} (hσ : 0 < σ.im) : thetaFour σ ≠ 0 := by
  refine not_of_iterate (P := fun s => thetaFour s = 0) (fun s hs h0 => ?_) 1
    (fun s hs h0 => ?_) hσ
  · have := landen_three_four hs
    rw [h0, mul_zero] at this
    exact (pow_eq_zero_iff two_ne_zero).mp this.symm
  · have := norm_thetaFour_sub_one_le hs
    rw [h0, zero_sub, norm_neg, norm_one] at this
    linarith [exp_neg_pi_le_quarter hs]

theorem thetaThree_ne_zero {σ : ℂ} (hσ : 0 < σ.im) : thetaThree σ ≠ 0 := by
  intro h0
  have := landen_three_four hσ
  rw [h0, zero_mul] at this
  exact thetaFour_ne_zero (two_mul_im_pos hσ) ((pow_eq_zero_iff two_ne_zero).mp this.symm)

theorem thT_ne_zero {σ : ℂ} (hσ : 0 < σ.im) : thT σ ≠ 0 := by
  refine not_of_iterate (P := fun s => thT s = 0) (fun s hs h0 => ?_) 1
    (fun s hs h0 => ?_) hσ
  · have := landen_two hs
    rw [thetaTwo_eq s, h0, mul_zero, zero_pow two_ne_zero] at this
    have h3 := thetaThree_ne_zero (two_mul_im_pos hs)
    have : thetaTwo (2 * s) = 0 := by
      rcases mul_eq_zero.mp this.symm with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · norm_num at h'
        · exact h'
      · exact absurd h h3
    rw [thetaTwo_eq] at this
    exact (mul_eq_zero.mp this).resolve_left (Complex.exp_ne_zero _)
  · have := norm_thT_sub_two_le hs
    rw [h0, zero_sub, norm_neg, Complex.norm_two] at this
    linarith [exp_neg_pi_le_quarter hs]

theorem thetaTwo_ne_zero {σ : ℂ} (hσ : 0 < σ.im) : thetaTwo σ ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (thT_ne_zero hσ)

/-! ## The Landen recursion for `F = h'/h − (πi/4) θ₄⁴` -/

/-- `h = θ₂/θ₃`. -/
def hq (s : ℂ) : ℂ := thetaTwo s / thetaThree s

/-- `F = h'/h − (πi/4) θ₄⁴`; Jacobi's formula is `F = 0`. -/
def Fq (s : ℂ) : ℂ := deriv hq s / hq s - π * I / 4 * thetaFour s ^ 4

lemma differentiableAt_hq {s : ℂ} (hs : 0 < s.im) : DifferentiableAt ℂ hq s :=
  (differentiableAt_thetaTwo' hs).div (differentiableAt_thetaThree' hs) (thetaThree_ne_zero hs)

lemma hq_ne_zero {s : ℂ} (hs : 0 < s.im) : hq s ≠ 0 :=
  div_ne_zero (thetaTwo_ne_zero hs) (thetaThree_ne_zero hs)

lemma hq_rel {s : ℂ} (hs : 0 < s.im) : hq s ^ 2 * (1 + hq (2 * s) ^ 2) = 2 * hq (2 * s) := by
  have hA := thetaThree_ne_zero (two_mul_im_pos hs)
  have hS := thetaThree_ne_zero hs
  have L1 := landen_three hs
  have L3 := landen_two hs
  have hsum : thetaThree (2 * s) ^ 2 + thetaTwo (2 * s) ^ 2 ≠ 0 := by
    rw [← L1]; exact pow_ne_zero 2 hS
  simp only [hq, div_pow]
  rw [L3, L1]
  field_simp

theorem Fq_rec {τ : ℂ} (hτ : 0 < τ.im) :
    Fq τ = thetaFour τ ^ 2 / thetaThree τ ^ 2 * Fq (2 * τ) := by
  have h2 := two_mul_im_pos hτ
  have hd1 := (differentiableAt_hq hτ).hasDerivAt
  have hd2 : HasDerivAt (fun s => hq (2 * s)) (deriv hq (2 * τ) * 2) τ := by
    have := (differentiableAt_hq h2).hasDerivAt.comp τ ((hasDerivAt_id τ).const_mul (2 : ℂ))
    rw [mul_one] at this
    exact this
  have hφ := ((hd1.mul hd1).mul ((hd2.mul hd2).const_add 1)).sub (hd2.const_mul 2)
  have h0 : HasDerivAt (fun s => hq s * hq s * (1 + hq (2 * s) * hq (2 * s)) - 2 * hq (2 * s))
      0 τ := by
    apply (hasDerivAt_const τ (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hτ] with s hs
    have := hq_rel hs
    linear_combination this
  have key := hφ.unique h0
  simp only [Pi.mul_apply] at key
  have R := hq_rel hτ
  have hs0 := hq_ne_zero hτ
  have hr0 := hq_ne_zero h2
  have h1r : 1 + hq (2 * τ) ^ 2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at R
    exact hr0 (by linear_combination -R / 2)
  have K : 2 * hq τ * deriv hq τ * (1 + hq (2 * τ) ^ 2) + 4 * hq τ ^ 2 * hq (2 * τ) *
      deriv hq (2 * τ) - 4 * deriv hq (2 * τ) = 0 := by linear_combination key
  have e1 : deriv hq τ / hq τ = deriv hq (2 * τ) * (1 - hq (2 * τ) ^ 2) /
      (hq (2 * τ) * (1 + hq (2 * τ) ^ 2)) := by
    rw [div_eq_div_iff hs0 (mul_ne_zero hr0 h1r)]
    linear_combination (hq τ * (1 + hq (2 * τ) ^ 2) / 4) * K -
      (deriv hq τ * (1 + hq (2 * τ) ^ 2) / 2 + hq τ * hq (2 * τ) * deriv hq (2 * τ)) * R
  have L1 := landen_three hτ
  have L2 := landen_four hτ
  have Q := jacobi_quartic h2
  have hA := thetaThree_ne_zero h2
  have hB := thetaTwo_ne_zero h2
  have hsum : thetaThree (2 * τ) ^ 2 + thetaTwo (2 * τ) ^ 2 ≠ 0 := by
    rw [← L1]; exact pow_ne_zero 2 (thetaThree_ne_zero hτ)
  unfold Fq
  rw [e1, show thetaFour τ ^ 4 = (thetaFour τ ^ 2) ^ 2 by ring, L2, L1,
    show thetaFour (2 * τ) ^ 4 = thetaThree (2 * τ) ^ 4 - thetaTwo (2 * τ) ^ 4 by
      linear_combination -Q]
  simp only [hq]
  field_simp
  ring

/-! ## `F = O(e^{−π Im σ})` -/

lemma logDeriv_hq {σ : ℂ} (hσ : 0 < σ.im) :
    deriv hq σ / hq σ = π * I / 4 + deriv thT σ / thT σ - deriv thetaThree σ / thetaThree σ := by
  have hT := thT_ne_zero hσ
  have h3 := thetaThree_ne_zero hσ
  have hE0 := Complex.exp_ne_zero (π * I * σ / 4)
  have hE : HasDerivAt (fun s : ℂ => cexp (π * I * s / 4))
      (cexp (π * I * σ / 4) * (π * I * 1 / 4)) σ :=
    (((hasDerivAt_id σ).const_mul (π * I : ℂ)).div_const 4).cexp
  have hd := (hE.mul (differentiableAt_thT hσ).hasDerivAt).div
    (differentiableAt_thetaThree' hσ).hasDerivAt h3
  have : deriv hq σ = _ := hd.deriv
  simp only [Pi.mul_apply] at this
  rw [this]
  simp only [hq, thetaTwo_eq]
  field_simp

lemma norm_one_sub_pow_four_le {x : ℂ} (hx : ‖x - 1‖ ≤ 1) : ‖1 - x ^ 4‖ ≤ 15 * ‖x - 1‖ := by
  have hx2 : ‖x‖ ≤ 2 := by
    calc ‖x‖ = ‖(x - 1) + 1‖ := by ring_nf
      _ ≤ ‖x - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have e3 : ‖x ^ 3‖ ≤ 8 := by
    rw [norm_pow]
    calc ‖x‖ ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hx2 3
      _ = 8 := by norm_num
  have e2 : ‖x ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    calc ‖x‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx2 2
      _ = 4 := by norm_num
  have hp : ‖x ^ 3 + x ^ 2 + x + 1‖ ≤ 15 := by
    linarith [norm_add_le (x ^ 3 + x ^ 2 + x) 1, norm_add_le (x ^ 3 + x ^ 2) x,
      norm_add_le (x ^ 3) (x ^ 2), norm_one (α := ℂ)]
  rw [show 1 - x ^ 4 = -((x - 1) * (x ^ 3 + x ^ 2 + x + 1)) by ring, norm_neg, norm_mul]
  calc ‖x - 1‖ * ‖x ^ 3 + x ^ 2 + x + 1‖ ≤ ‖x - 1‖ * 15 :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = 15 * ‖x - 1‖ := mul_comm _ _

lemma one_le_norm_thT {σ : ℂ} (hσ : 1 ≤ σ.im) : 1 ≤ ‖thT σ‖ := by
  have h := norm_thT_sub_two_le hσ
  have hq := exp_neg_pi_le_quarter hσ
  have : ‖(2 : ℂ)‖ ≤ ‖thT σ‖ + ‖thT σ - 2‖ := by
    calc ‖(2 : ℂ)‖ = ‖thT σ - (thT σ - 2)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  rw [Complex.norm_two] at this
  linarith

lemma quarter_le_norm_thetaThree {σ : ℂ} (hσ : 1 ≤ σ.im) : 1 / 4 ≤ ‖thetaThree σ‖ := by
  have h := norm_thetaThree_sub_one_le hσ
  have hq := exp_neg_pi_le_quarter hσ
  have : ‖(1 : ℂ)‖ ≤ ‖thetaThree σ‖ + ‖thetaThree σ - 1‖ := by
    calc ‖(1 : ℂ)‖ = ‖thetaThree σ - (thetaThree σ - 1)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  rw [norm_one] at this
  linarith

lemma norm_thetaFour_le {σ : ℂ} (hσ : 1 ≤ σ.im) : ‖thetaFour σ‖ ≤ 7 / 4 := by
  have h := norm_thetaFour_sub_one_le hσ
  have hq := exp_neg_pi_le_quarter hσ
  have : ‖thetaFour σ‖ ≤ ‖thetaFour σ - 1‖ + ‖(1 : ℂ)‖ := by
    calc ‖thetaFour σ‖ = ‖(thetaFour σ - 1) + 1‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  rw [norm_one] at this
  linarith

/-- The constant in `‖F σ‖ ≤ C e^{−π Im σ}`. -/
def Cq : ℝ := 15 * rexp π + 12 * π

theorem norm_Fq_le {σ : ℂ} (hσ : 2 ≤ σ.im) : ‖Fq σ‖ ≤ Cq * rexp (-π * σ.im) := by
  have hσ0 : 0 < σ.im := by linarith
  have hσ1 : 1 ≤ σ.im := by linarith
  have hr0 : 0 ≤ rexp (-π * σ.im) := (Real.exp_pos _).le
  have hrq : rexp (-π * σ.im) ≤ 1 / 4 := exp_neg_pi_le_quarter hσ1
  have h4 := norm_thetaFour_sub_one_le hσ1
  have dT := norm_deriv_le_of_bound (fun z hz => differentiableAt_thT hz)
    (fun z hz => norm_thT_sub_two_le hz) hσ
  have d3 := norm_deriv_le_of_bound (fun z hz => differentiableAt_thetaThree' hz)
    (fun z hz => norm_thetaThree_sub_one_le hz) hσ
  have lT := one_le_norm_thT hσ1
  have l3 := quarter_le_norm_thetaThree hσ1
  have q4 := norm_one_sub_pow_four_le (by linarith : ‖thetaFour σ - 1‖ ≤ 1)
  have hπ := Real.pi_pos
  have heπ := Real.exp_pos π
  rw [Fq, logDeriv_hq hσ0]
  have eq : π * I / 4 + deriv thT σ / thT σ - deriv thetaThree σ / thetaThree σ -
      π * I / 4 * thetaFour σ ^ 4 = deriv thT σ / thT σ - deriv thetaThree σ / thetaThree σ +
      π * I / 4 * (1 - thetaFour σ ^ 4) := by ring
  rw [eq]
  have n1 : ‖deriv thT σ / thT σ‖ ≤ 3 * rexp π * rexp (-π * σ.im) := by
    rw [norm_div]
    calc ‖deriv thT σ‖ / ‖thT σ‖ ≤ ‖deriv thT σ‖ / 1 :=
          div_le_div_of_nonneg_left (norm_nonneg _) one_pos lT
      _ ≤ _ := by rw [div_one]; exact dT
  have n2 : ‖deriv thetaThree σ / thetaThree σ‖ ≤ 4 * (3 * rexp π * rexp (-π * σ.im)) := by
    rw [norm_div]
    calc ‖deriv thetaThree σ‖ / ‖thetaThree σ‖ ≤ ‖deriv thetaThree σ‖ / (1 / 4) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) l3
      _ = 4 * ‖deriv thetaThree σ‖ := by ring
      _ ≤ _ := by linarith
  have n3 : ‖π * I / 4 * (1 - thetaFour σ ^ 4)‖ ≤ π / 4 * (15 * (3 * rexp (-π * σ.im))) := by
    rw [norm_mul]
    have : ‖(π : ℂ) * I / 4‖ = π / 4 := by
      rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hπ.le]
      norm_num
    rw [this]
    gcongr
    linarith
  have ns := norm_sub_le (deriv thT σ / thT σ) (deriv thetaThree σ / thetaThree σ)
  calc ‖deriv thT σ / thT σ - deriv thetaThree σ / thetaThree σ +
        π * I / 4 * (1 - thetaFour σ ^ 4)‖
      ≤ ‖deriv thT σ / thT σ‖ + ‖deriv thetaThree σ / thetaThree σ‖ +
        ‖π * I / 4 * (1 - thetaFour σ ^ 4)‖ :=
        (norm_add_le _ _).trans (by linarith)
    _ ≤ 3 * rexp π * rexp (-π * σ.im) + 4 * (3 * rexp π * rexp (-π * σ.im)) +
        π / 4 * (15 * (3 * rexp (-π * σ.im))) := by linarith
    _ ≤ Cq * rexp (-π * σ.im) := by
        unfold Cq
        nlinarith [mul_nonneg hπ.le hr0]

/-! ## `F = 0` -/

lemma exp_neg_pi_le_small {t : ℝ} (ht : 43 ≤ t) : rexp (-π * t) ≤ 1 / 128 := by
  have h3 := Real.pi_gt_three
  have h1 : 128 ≤ rexp (π * t) := by
    nlinarith [Real.add_one_le_exp (π * t), mul_le_mul h3.le ht (by norm_num) Real.pi_pos.le]
  rw [show -π * t = -(π * t) by ring, Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) h1

lemma norm_rho_le {σ : ℂ} (hσ : 1 ≤ σ.im) : ‖thetaFour σ ^ 2 / thetaThree σ ^ 2‖ ≤ 64 := by
  have a := pow_le_pow_left₀ (norm_nonneg _) (norm_thetaFour_le hσ) 2
  have b := pow_le_pow_left₀ (by norm_num) (quarter_le_norm_thetaThree hσ) 2
  have hb : 0 < ‖thetaThree σ‖ ^ 2 := lt_of_lt_of_le (by norm_num) b
  rw [norm_div, norm_pow, norm_pow, div_le_iff₀ hb]
  nlinarith

theorem Fq_eq_zero_of_large {σ : ℂ} (hσ : 43 ≤ σ.im) : Fq σ = 0 := by
  have hC : 0 ≤ Cq := by unfold Cq; positivity
  have claim : ∀ k : ℕ, ∀ s : ℂ, 43 ≤ s.im →
      ‖Fq s‖ ≤ Cq * rexp (-π * s.im) * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => intro s hs; simpa using norm_Fq_le (by linarith : 2 ≤ s.im)
    | succ k ih =>
      intro s hs
      have hs0 : 0 < s.im := by linarith
      have him : (2 * s).im = 2 * s.im := by simp
      have h2s : 43 ≤ (2 * s).im := by rw [him]; linarith
      have := ih _ h2s
      rw [Fq_rec hs0, norm_mul]
      have hρ := norm_rho_le (by linarith : 1 ≤ s.im)
      rw [him, show -π * (2 * s.im) = -π * s.im + -π * s.im by ring, Real.exp_add] at this
      have hsm := exp_neg_pi_le_small hs
      have hr0 := (Real.exp_pos (-π * s.im)).le
      have hp : 0 ≤ Cq * rexp (-π * s.im) * (1 / 2) ^ k := by positivity
      calc ‖thetaFour s ^ 2 / thetaThree s ^ 2‖ * ‖Fq (2 * s)‖
          ≤ 64 * (Cq * (rexp (-π * s.im) * rexp (-π * s.im)) * (1 / 2) ^ k) :=
            mul_le_mul hρ this (norm_nonneg _) (by norm_num)
        _ = (64 * rexp (-π * s.im)) * (Cq * rexp (-π * s.im) * (1 / 2) ^ k) := by ring
        _ ≤ (1 / 2) * (Cq * rexp (-π * s.im) * (1 / 2) ^ k) :=
            mul_le_mul_of_nonneg_right (by linarith) hp
        _ = Cq * rexp (-π * s.im) * (1 / 2) ^ (k + 1) := by ring
  have ht : Tendsto (fun k : ℕ => Cq * rexp (-π * σ.im) * (1 / 2) ^ k) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (Cq * rexp (-π * σ.im))
    rwa [mul_zero] at this
  exact norm_le_zero_iff.mp (ge_of_tendsto' ht (fun k => claim k σ hσ))

theorem Fq_eq_zero {τ : ℂ} (hτ : 0 < τ.im) : Fq τ = 0 := by
  by_contra hne
  exact not_of_iterate (P := fun s => Fq s ≠ 0)
    (fun s hs h h2 => h (by rw [Fq_rec hs, h2, mul_zero])) 43
    (fun s hs h => h (Fq_eq_zero_of_large hs)) hτ hne

/-- **Jacobi's derivative formula** `dλ/dt = πi λ θ₄⁴`, `λ = θ₂⁴/θ₃⁴` (statement of
`ZInQ.GZWeil.JacobiLambdaDeriv`). -/
theorem jacobiLambdaDeriv' : ∀ t : ℂ, 0 < t.im → HasDerivAt
    (fun s => thetaTwo s ^ 4 / thetaThree s ^ 4)
    (π * I * (thetaTwo t ^ 4 / thetaThree t ^ 4) * thetaFour t ^ 4) t := by
  intro t ht
  have hF := Fq_eq_zero ht
  have hs0 := hq_ne_zero ht
  have ha : deriv hq t = π * I / 4 * hq t * thetaFour t ^ 4 := by
    have h1 := sub_eq_zero.mp hF
    rw [div_eq_iff hs0] at h1
    rw [h1]; ring
  have hfun : (fun s => thetaTwo s ^ 4 / thetaThree s ^ 4) = fun s => hq s ^ 4 :=
    funext fun s => (div_pow _ _ _).symm
  rw [hfun]
  have := (differentiableAt_hq ht).hasDerivAt.pow 4
  convert this using 1
  rw [ha]
  simp only [hq]
  push_cast
  ring

end ZInQ.JacobiLambda

namespace ZInQ.GZWeil

/-- **Jacobi's derivative formula `dλ/dt = πi λ θ₄⁴` (gz-weil's printed leaf), proved.** -/
theorem jacobiLambdaDeriv : JacobiLambdaDeriv := ZInQ.JacobiLambda.jacobiLambdaDeriv'

/-- x0-32's `X0.EtaModelDifferential` (`x' = 4πi f₁ y`), now unconditional. -/
theorem etaModelDifferential : ZInQ.Contrib.TYZGenus.X0.EtaModelDifferential :=
  etaModelDifferential_of_jacobiLambdaDeriv jacobiLambdaDeriv

/-- gz-weil's `ModularParamC1`, now unconditional. -/
theorem modularParamC1 : ModularParamC1 :=
  modularParamC1_of_jacobiLambdaDeriv jacobiLambdaDeriv

/-- gz-hl3's `ShimuraCMParamCd` (the analytic modular parametrization of every `C_d`,
`d ≡ 5 (mod 8)` squarefree), now unconditional. -/
theorem shimuraCMParamCd : ZInQ.GZHL3.ShimuraCMParamCd :=
  shimuraCMParamCd_of_jacobiLambdaDeriv jacobiLambdaDeriv

/-- `GZStatements.GrossZagierHeegnerCd` from four leaves (gz-weil's five minus Jacobi's formula). -/
theorem grossZagierHeegnerCd_of_leaves4 (hU : ZInQ.GZHL3.WeierstrassUniformization)
    (hHP : ZInQ.GZHL3.HeegnerPointRationalCd)
    (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd :=
  grossZagierHeegnerCd_of_printed hU jacobiLambdaDeriv hHP hGZ hGC

end ZInQ.GZWeil
