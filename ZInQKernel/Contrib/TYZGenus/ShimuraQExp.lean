import ZInQKernel.Contrib.TYZGenus.ShimuraModFn

/-!
# tyz-cm: the rational `q`-expansions of x0-32's coordinate functions `x, y` (proved)

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

Proves `XQExpRational` and `YQExpRational` (`ShimuraModFn.lean`): `q²·x(τ)` and `q³·y(τ)` are
power series in `q = e^{2πiτ}` with rational coefficients, converging on all of `ℍ`.

Method: a function holomorphic on the unit disc whose Taylor coefficients at `0` are rational
has a rational `q`-expansion on the disc (`Complex.hasSum_taylorSeries_on_ball`). Functions with
rational iterated derivatives at `0` (`IsRatAt`) are closed under sums, products and inverses
(Leibniz rule); the products `p_d(q) = ∏ₙ (1 − q^{d(n+1)})` are `IsRatAt`, because the iterated
derivatives at `0` of the finite products are rational and stabilize, and they converge to those
of `p_d` (locally uniform convergence of the products, Weierstrass). Then
`q²x = p₂²p₁₆/(p₄p₃₂²) + 2q²` and `q³y = −p₈⁴p₁₆²/(p₄²p₃₂⁴)` (`η(dτ) = q^{d/24}p_d(q)`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open Complex Filter Topology Metric

/-! ## Functions with rational Taylor coefficients at `0` -/

/-- `ℚ ⊆ ℂ` as a subfield. -/
abbrev Qc : Subfield ℂ := (algebraMap ℚ ℂ).fieldRange

/-- `F` is `C^∞` at `0` and its iterated derivatives at `0` are rational. -/
def IsRatAt (F : ℂ → ℂ) : Prop :=
  (∀ n : ℕ, ContDiffAt ℂ n F 0) ∧ ∀ n : ℕ, iteratedDeriv n F 0 ∈ Qc

theorem natCast_mem_Qc (n : ℕ) : (n : ℂ) ∈ Qc := ⟨n, by simp⟩

theorem ratCast_mem_Qc (r : ℚ) : (r : ℂ) ∈ Qc := ⟨r, by simp⟩

theorem isRatAt_const (r : ℚ) : IsRatAt fun _ => (r : ℂ) := by
  refine ⟨fun n => contDiffAt_const, fun n => ?_⟩
  rcases n with _ | n
  · simp
  · simp [iteratedDeriv_const]

theorem isRatAt_pow (k : ℕ) : IsRatAt fun q : ℂ => q ^ k := by
  refine ⟨fun n => (contDiff_id.pow k).contDiffAt, fun n => ?_⟩
  rw [iteratedDeriv_fun_pow_zero (𝕜 := ℂ)]
  split_ifs <;> exact natCast_mem_Qc _

theorem IsRatAt.add {F G : ℂ → ℂ} (hF : IsRatAt F) (hG : IsRatAt G) :
    IsRatAt fun q => F q + G q := by
  refine ⟨fun n => (hF.1 n).add (hG.1 n), fun n => ?_⟩
  rw [iteratedDeriv_fun_add (hF.1 n) (hG.1 n)]
  exact Subfield.add_mem _ (hF.2 n) (hG.2 n)

theorem IsRatAt.mul {F G : ℂ → ℂ} (hF : IsRatAt F) (hG : IsRatAt G) :
    IsRatAt fun q => F q * G q := by
  refine ⟨fun n => (hF.1 n).mul (hG.1 n), fun n => ?_⟩
  rw [iteratedDeriv_fun_mul (hF.1 n) (hG.1 n)]
  exact Subfield.sum_mem _ fun i _ =>
    Subfield.mul_mem _ (Subfield.mul_mem _ (natCast_mem_Qc _) (hF.2 i)) (hG.2 _)

theorem IsRatAt.neg {F : ℂ → ℂ} (hF : IsRatAt F) : IsRatAt fun q => -F q := by
  have := (isRatAt_const (-1)).mul hF
  simpa using this

theorem IsRatAt.pow {F : ℂ → ℂ} (hF : IsRatAt F) (k : ℕ) : IsRatAt fun q => F q ^ k := by
  induction k with
  | zero => simpa using isRatAt_const 1
  | succ k ih => simpa [pow_succ] using ih.mul hF

theorem IsRatAt.inv {F : ℂ → ℂ} (hF : IsRatAt F) (h0 : F 0 ≠ 0) :
    IsRatAt fun q => (F q)⁻¹ := by
  have hG : ∀ n : ℕ, ContDiffAt ℂ n (fun q => (F q)⁻¹) 0 := fun n => (hF.1 n).inv h0
  refine ⟨hG, fun n => ?_⟩
  -- `F · F⁻¹ = 1` near `0`
  have hev : (fun q => F q * (F q)⁻¹) =ᶠ[𝓝 0] fun _ => (1 : ℂ) := by
    have hc : ContinuousAt F 0 := (hF.1 0).continuousAt
    filter_upwards [hc.eventually_ne h0] with q hq
    exact mul_inv_cancel₀ hq
  have hF0 : iteratedDeriv 0 F 0 ∈ Qc := hF.2 0
  rw [iteratedDeriv_zero] at hF0
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [iteratedDeriv_zero]
      exact Subfield.inv_mem _ hF0
    · have hL := hev.iteratedDeriv_eq (n + 1)
      rw [iteratedDeriv_fun_mul (hF.1 _) (hG _), Finset.sum_range_succ'] at hL
      have h1 : iteratedDeriv (n + 1) (fun _ : ℂ => (1 : ℂ)) 0 = 0 := by
        rw [iteratedDeriv_succ']; simp
      rw [h1] at hL
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
        Nat.sub_zero] at hL
      -- `F 0 · G⁽ⁿ⁺¹⁾(0) = −Σ …`
      have hS : (∑ i ∈ Finset.range (n + 1), ((n + 1).choose (i + 1) : ℂ) *
          iteratedDeriv (i + 1) F 0 * iteratedDeriv (n + 1 - (i + 1)) (fun q => (F q)⁻¹) 0) ∈ Qc :=
        Subfield.sum_mem _ fun i hi =>
          Subfield.mul_mem _ (Subfield.mul_mem _ (natCast_mem_Qc _) (hF.2 _))
            (ih _ (by have := Finset.mem_range.1 hi; omega))
      set S := ∑ i ∈ Finset.range (n + 1), ((n + 1).choose (i + 1) : ℂ) *
          iteratedDeriv (i + 1) F 0 * iteratedDeriv (n + 1 - (i + 1)) (fun q => (F q)⁻¹) 0
      set G := iteratedDeriv (n + 1) (fun q => (F q)⁻¹) 0
      have h2 : F 0 * G = -S := by linear_combination hL
      have heq : G = -(F 0)⁻¹ * S := by
        calc G = (F 0)⁻¹ * (F 0 * G) := by rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]
          _ = -(F 0)⁻¹ * S := by rw [h2]; ring
      rw [heq]
      exact Subfield.mul_mem _ (Subfield.neg_mem _ (Subfield.inv_mem _ hF0)) hS

theorem IsRatAt.div {F G : ℂ → ℂ} (hF : IsRatAt F) (hG : IsRatAt G) (h0 : G 0 ≠ 0) :
    IsRatAt fun q => F q / G q := by
  simpa [div_eq_mul_inv] using hF.mul (hG.inv h0)

/-- Iterated derivatives of locally uniform limits of holomorphic functions converge. -/
theorem tendsto_iteratedDeriv {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) (n : ℕ) :
    ∀ {Fs : ℕ → ℂ → ℂ} {F : ℂ → ℂ}, TendstoLocallyUniformlyOn Fs F atTop U →
      (∀ M, DifferentiableOn ℂ (Fs M) U) →
      Tendsto (fun M => iteratedDeriv n (Fs M) z) atTop (𝓝 (iteratedDeriv n F z)) := by
  induction n with
  | zero =>
    intro Fs F h _
    simpa using h.tendsto_at hz
  | succ n ih =>
    intro Fs F h hd
    simp only [iteratedDeriv_succ']
    exact ih (h.deriv (Eventually.of_forall hd) hU) fun M => (hd M).deriv hU

/-- If `F_M → F` locally uniformly on the unit disc, the `F_M` are holomorphic and `IsRatAt`, and
for each `n` the `n`-th derivatives at `0` are eventually constant, then `F` has rational
iterated derivatives at `0`. -/
theorem iteratedDeriv_mem_of_limit {Fs : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (h : TendstoLocallyUniformlyOn Fs F atTop (ball (0 : ℂ) 1))
    (hd : ∀ M, DifferentiableOn ℂ (Fs M) (ball (0 : ℂ) 1)) (hR : ∀ M, IsRatAt (Fs M))
    (hst : ∀ n, ∀ᶠ M in atTop, iteratedDeriv n (Fs M) 0 = iteratedDeriv n (Fs n) 0) (n : ℕ) :
    iteratedDeriv n F 0 ∈ Qc := by
  have ht := tendsto_iteratedDeriv isOpen_ball (mem_ball_self one_pos) n h hd
  have hc : Tendsto (fun M => iteratedDeriv n (Fs M) 0) atTop (𝓝 (iteratedDeriv n (Fs n) 0)) :=
    tendsto_const_nhds.congr' (by filter_upwards [hst n] with M hM; exact hM.symm)
  rw [tendsto_nhds_unique ht hc]
  exact (hR n).2 n

/-! ## The products `p_d(q) = ∏ₙ (1 − q^{d(n+1)})` -/

/-- The finite product `∏_{i < M} (1 − (q^d)^{i+1})`. -/
def finP (d M : ℕ) (q : ℂ) : ℂ := ∏ i ∈ Finset.range M, (1 - (q ^ d) ^ (i + 1))

/-- `p_d(q) = F(q^d)`, `F = X0.prodF`. -/
def pd (d : ℕ) (q : ℂ) : ℂ := X0.prodF (q ^ d)

theorem finP_succ (d M : ℕ) :
    finP d (M + 1) = fun q => finP d M q * ((1 : ℚ) + -(q ^ (d * (M + 1)))) := by
  funext q
  simp [finP, Finset.prod_range_succ, ← pow_mul, sub_eq_add_neg]

theorem isRatAt_finP (d M : ℕ) : IsRatAt (finP d M) := by
  induction M with
  | zero =>
    have : finP d 0 = fun _ => ((1 : ℚ) : ℂ) := by funext q; simp [finP]
    rw [this]; exact isRatAt_const 1
  | succ M ih =>
    rw [finP_succ]
    exact ih.mul ((isRatAt_const 1).add (isRatAt_pow _).neg)

theorem differentiable_finP (d M : ℕ) : Differentiable ℂ (finP d M) := by
  unfold finP
  fun_prop

/-- Stability: `(finP d (M+1))⁽ⁿ⁾(0) = (finP d M)⁽ⁿ⁾(0)` for `n < d(M+1)`. -/
theorem iteratedDeriv_finP_succ (d M n : ℕ) (hn : n < d * (M + 1)) :
    iteratedDeriv n (finP d (M + 1)) 0 = iteratedDeriv n (finP d M) 0 := by
  rw [finP_succ]
  have h1 := (isRatAt_finP d M).1 n
  have h2 : ContDiffAt ℂ n (fun q : ℂ => ((1 : ℚ) : ℂ) + -q ^ (d * (M + 1))) 0 :=
    (((isRatAt_const 1).add (isRatAt_pow _).neg).1 n)
  rw [iteratedDeriv_fun_mul h1 h2]
  have hk : d * (M + 1) ≠ 0 := by omega
  have hz : ∀ i : ℕ, i ≤ n → i ≠ 0 →
      iteratedDeriv i (fun q : ℂ => ((1 : ℚ) : ℂ) + -q ^ (d * (M + 1))) 0 = 0 := by
    intro i hi hi0
    rw [iteratedDeriv_fun_add contDiffAt_const ((contDiff_id.pow _).neg.contDiffAt),
      iteratedDeriv_fun_neg, iteratedDeriv_const,
      iteratedDeriv_fun_pow_zero (𝕜 := ℂ)]
    rw [if_neg hi0, if_neg (show i ≠ d * (M + 1) by omega)]
    simp
  rw [Finset.sum_eq_single_of_mem n (by simp) ?_]
  · simp [hk]
  · intro i hi hne
    have hi' := Finset.mem_range.1 hi
    rw [hz (n - i) (by omega) (by omega), mul_zero]

theorem pd_zero (d : ℕ) (hd : 0 < d) : pd d 0 = 1 := by
  simp [pd, X0.prodF, zero_pow hd.ne']

theorem prodF_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : X0.prodF q ≠ 0 := by
  unfold X0.prodF
  simp_rw [sub_eq_add_neg]
  refine tprod_one_add_ne_zero_of_summable (f := fun n => -q ^ (n + 1)) (fun i => ?_) ?_
  · intro h
    have : q ^ (i + 1) = 1 := by linear_combination -h
    have h1 : ‖q ^ (i + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    rw [this, norm_one] at h1
    exact lt_irrefl _ h1
  · simpa [norm_pow] using (summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (norm_nonneg _) hq)

theorem pow_mem_ball {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) {d : ℕ} (hd : 0 < d) :
    q ^ d ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at hq ⊢
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hq hd.ne'

theorem pd_ne_zero {d : ℕ} (hd : 0 < d) {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) : pd d q ≠ 0 :=
  prodF_ne_zero (mem_ball_zero_iff.1 (pow_mem_ball hq hd))

theorem differentiableOn_pd {d : ℕ} (hd : 0 < d) : DifferentiableOn ℂ (pd d) (ball (0 : ℂ) 1) := by
  have := ModularForm.differentiableOn_tprod_one_sub_pow.comp (differentiable_pow d).differentiableOn
    (fun q hq => pow_mem_ball hq hd)
  exact this

theorem tendsto_finP {d : ℕ} (hd : 0 < d) :
    TendstoLocallyUniformlyOn (finP d) (pd d) atTop (ball (0 : ℂ) 1) := by
  have h := (ModularForm.multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.comp
    (fun q : ℂ => q ^ d) (fun q hq => pow_mem_ball hq hd)
      (continuous_pow d).continuousOn).tendstoLocallyUniformlyOn_finsetRange
  exact h

theorem isRatAt_pd {d : ℕ} (hd : 0 < d) : IsRatAt (pd d) := by
  have hc : ∀ n : ℕ, ContDiffAt ℂ n (pd d) 0 := fun n =>
    ((differentiableOn_pd hd).contDiffOn isOpen_ball).contDiffAt
      (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  refine ⟨hc, iteratedDeriv_mem_of_limit (tendsto_finP hd)
    (fun M => (differentiable_finP d M).differentiableOn) (isRatAt_finP d) (fun n => ?_)⟩
  rw [eventually_atTop]
  refine ⟨n, fun M hM => ?_⟩
  induction M, hM using Nat.le_induction with
  | base => rfl
  | succ M hM ih =>
    rw [iteratedDeriv_finP_succ d M n (by nlinarith), ih]

/-! ## Rational `q`-expansions on the unit disc -/

/-- **A holomorphic function on the unit disc with rational Taylor coefficients at `0` has a
rational power series expansion on the disc.** -/
theorem exists_rat_hasSum {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hR : IsRatAt F) :
    ∃ a : ℕ → ℚ, ∀ q ∈ ball (0 : ℂ) 1, HasSum (fun n : ℕ => (a n : ℂ) * q ^ n) (F q) := by
  choose r hr using fun n => hR.2 n
  refine ⟨fun n => r n / n.factorial, fun q hq => ?_⟩
  have := Complex.hasSum_taylorSeries_on_ball hd hq
  refine this.congr_fun fun n => ?_
  rw [← hr n]
  simp only [sub_zero, smul_eq_mul, Rat.cast_div, Rat.cast_natCast, eq_ratCast]
  ring

/-- `q²x(τ)` as a function of `q`. -/
def Fx (q : ℂ) : ℂ := pd 2 q ^ 2 * pd 16 q / (pd 4 q * pd 32 q ^ 2) + 2 * q ^ 2

/-- `q³y(τ)` as a function of `q`. -/
def Fy (q : ℂ) : ℂ := -(pd 8 q ^ 4 * pd 16 q ^ 2 / (pd 4 q ^ 2 * pd 32 q ^ 4))

theorem isRatAt_Fx : IsRatAt Fx := by
  have h2 : IsRatAt (pd 2) := isRatAt_pd (by norm_num)
  have h4 : IsRatAt (pd 4) := isRatAt_pd (by norm_num)
  have h16 : IsRatAt (pd 16) := isRatAt_pd (by norm_num)
  have h32 : IsRatAt (pd 32) := isRatAt_pd (by norm_num)
  have hN : IsRatAt fun q => pd 2 q ^ 2 * pd 16 q := (h2.pow 2).mul h16
  have hD : IsRatAt fun q => pd 4 q * pd 32 q ^ 2 := h4.mul (h32.pow 2)
  have hD0 : pd 4 0 * pd 32 0 ^ 2 ≠ 0 := by
    rw [pd_zero 4 (by norm_num), pd_zero 32 (by norm_num)]; norm_num
  have hT : IsRatAt fun q : ℂ => ((2 : ℚ) : ℂ) * q ^ 2 := (isRatAt_const 2).mul (isRatAt_pow 2)
  have h := (hN.div hD hD0).add hT
  have e : Fx = fun q => pd 2 q ^ 2 * pd 16 q / (pd 4 q * pd 32 q ^ 2) + ((2 : ℚ) : ℂ) * q ^ 2 := by
    funext q; simp [Fx]
  rw [e]; exact h

theorem isRatAt_Fy : IsRatAt Fy := by
  have h8 : IsRatAt (pd 8) := isRatAt_pd (by norm_num)
  have h4 : IsRatAt (pd 4) := isRatAt_pd (by norm_num)
  have h16 : IsRatAt (pd 16) := isRatAt_pd (by norm_num)
  have h32 : IsRatAt (pd 32) := isRatAt_pd (by norm_num)
  have hN : IsRatAt fun q => pd 8 q ^ 4 * pd 16 q ^ 2 := (h8.pow 4).mul (h16.pow 2)
  have hD : IsRatAt fun q => pd 4 q ^ 2 * pd 32 q ^ 4 := (h4.pow 2).mul (h32.pow 4)
  have hD0 : pd 4 0 ^ 2 * pd 32 0 ^ 4 ≠ 0 := by
    rw [pd_zero 4 (by norm_num), pd_zero 32 (by norm_num)]; norm_num
  exact (hN.div hD hD0).neg

theorem differentiableOn_Fx : DifferentiableOn ℂ Fx (ball (0 : ℂ) 1) := by
  have h2 := differentiableOn_pd (d := 2) (by norm_num)
  have h4 := differentiableOn_pd (d := 4) (by norm_num)
  have h16 := differentiableOn_pd (d := 16) (by norm_num)
  have h32 := differentiableOn_pd (d := 32) (by norm_num)
  unfold Fx
  refine DifferentiableOn.add ?_ (((differentiable_pow 2).differentiableOn).const_mul 2)
  refine DifferentiableOn.div ((h2.pow 2).mul h16) (h4.mul (h32.pow 2)) fun q hq => ?_
  exact mul_ne_zero (pd_ne_zero (by norm_num) hq) (pow_ne_zero _ (pd_ne_zero (by norm_num) hq))

theorem differentiableOn_Fy : DifferentiableOn ℂ Fy (ball (0 : ℂ) 1) := by
  have h8 := differentiableOn_pd (d := 8) (by norm_num)
  have h4 := differentiableOn_pd (d := 4) (by norm_num)
  have h16 := differentiableOn_pd (d := 16) (by norm_num)
  have h32 := differentiableOn_pd (d := 32) (by norm_num)
  unfold Fy
  refine DifferentiableOn.neg ?_
  refine DifferentiableOn.div ((h8.pow 4).mul (h16.pow 2)) ((h4.pow 2).mul (h32.pow 4))
    fun q hq => ?_
  exact mul_ne_zero (pow_ne_zero _ (pd_ne_zero (by norm_num) hq))
    (pow_ne_zero _ (pd_ne_zero (by norm_num) hq))

/-! ## Back to `τ ∈ ℍ` -/

theorem qParam_natMul (d : ℕ) (z : ℂ) :
    Function.Periodic.qParam 1 ((d : ℂ) * z) = cexp (2 * Real.pi * I * z) ^ d := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem q_mem_ball (τ : UpperHalfPlane) : cexp (2 * Real.pi * I * τ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, Complex.norm_exp]
  have h1 : (2 * (Real.pi : ℂ) * I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h1]
  have := τ.im_pos
  have h2 : -(2 * Real.pi * τ.im) < 0 := by nlinarith [Real.pi_pos]
  calc Real.exp _ < Real.exp 0 := Real.exp_lt_exp.2 h2
    _ = 1 := Real.exp_zero

theorem pF_eq_pd (d : ℕ) (z : ℂ) : X0.pF d z = pd d (cexp (2 * Real.pi * I * z)) := by
  simp only [X0.pF, pd, qParam_natMul]

theorem q2_xC (τ : UpperHalfPlane) :
    cexp (2 * Real.pi * I * τ) ^ 2 * X0.xC τ = Fx (cexp (2 * Real.pi * I * τ)) := by
  rw [X0.xC_decomp]
  have h2 := pF_eq_pd 2 τ
  have h4 := pF_eq_pd 4 τ
  have h16 := pF_eq_pd 16 τ
  have h32 := pF_eq_pd 32 τ
  simp only [X0.pF, Nat.cast_ofNat] at h2 h4 h16 h32
  rw [h2, h4, h16, h32, Fx]
  have hq : cexp (2 * Real.pi * I * τ) ≠ 0 := Complex.exp_ne_zero _
  field_simp

theorem q3_yC (τ : UpperHalfPlane) :
    cexp (2 * Real.pi * I * τ) ^ 3 * X0.yC τ = Fy (cexp (2 * Real.pi * I * τ)) := by
  have hb := q_mem_ball τ
  have hw := X0.wz_ne_zero τ
  have hB : X0.pF 4 τ ^ 2 * X0.pF 32 τ ^ 4 ≠ 0 := by
    rw [pF_eq_pd, pF_eq_pd]
    exact mul_ne_zero (pow_ne_zero _ (pd_ne_zero (by norm_num) hb))
      (pow_ne_zero _ (pd_ne_zero (by norm_num) hb))
  have hyd : X0.yC τ = -(X0.pF 8 τ ^ 4 * X0.pF 16 τ ^ 2 / (X0.pF 4 τ ^ 2 * X0.pF 32 τ ^ 4)) /
      X0.wz τ ^ 72 := by
    unfold X0.yC
    rw [X0.etaD_eq'', X0.etaD_eq'', X0.etaD_eq'', X0.etaD_eq'']
    field_simp
  rw [hyd, Fy, ← pF_eq_pd, ← pF_eq_pd, ← pF_eq_pd, ← pF_eq_pd, ← X0.wz_pow_24]
  field_simp

/-- **`XQExpRational`, proved.** -/
theorem xQExpRational : XQExpRational := by
  obtain ⟨a, ha⟩ := exists_rat_hasSum differentiableOn_Fx isRatAt_Fx
  exact ⟨a, fun τ => by rw [q2_xC]; exact ha _ (q_mem_ball τ)⟩

/-- **`YQExpRational`, proved.** -/
theorem yQExpRational : YQExpRational := by
  obtain ⟨b, hb⟩ := exists_rat_hasSum differentiableOn_Fy isRatAt_Fy
  exact ⟨b, fun τ => by rw [q3_yC]; exact hb _ (q_mem_ball τ)⟩

/-- **The CM leaf from the general Shimura reciprocity law for `ℚ(X₀(N))`, x0-32's
`Γ₀(32)`-invariance leaf and the cusp-growth leaf** (the `q`-expansions are proved). -/
theorem cmFieldOfDefinition_of_modFn' (hS : ShimuraReciprocityModFn) (hI : X0.EtaModelInvariant)
    (hG : EtaCuspGrowth) : ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition RingClass.ringClassFieldD :=
  cmFieldOfDefinition_of_modFn hS hI hG xQExpRational yQExpRational

end ZInQ.Contrib.TYZGenus.Shimura
