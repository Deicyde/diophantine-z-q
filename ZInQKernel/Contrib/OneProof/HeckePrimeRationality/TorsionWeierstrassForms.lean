import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaG2Identity
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelPrincipalForms

/-!
# Weight-two modular forms from Weierstrass torsion values

For a positive level `N` and integers `a, b`, the function `τ ↦ xValue N a b τ` (the value of the
Weierstrass function `℘_τ` of the lattice `ℤ + ℤ τ` at `(a τ + b)/N`, and `0` when `N` divides
both `a` and `b`) is a modular form of weight two on `Γ(N)` (`xForm`). The quadratic value
`muValue = (lambdaValue² - xValue)/2` is likewise a weight-two form on `Γ(N)` (`muForm`).

Main steps.
* `℘_{τ+1}(z) = ℘_τ(z)` and `℘_{-1/τ}(z) = τ² ℘_τ(τ z)` off the lattice, from the theta
  transformation laws and `℘ = -(H'/H)' + c`; hence `x_{(a,b)} ∣[2] γ = x_{(a,b) γ}` for all
  `γ ∈ SL(2, ℤ)`, and invariance under `Γ(N)` by label periodicity.
* On admissible labels `x = (θ₁² - θ₀ θ₂)/θ₀² + c(τ)` with `θ_k` the termwise `z`-derivative
  series of `jacobiTheta₂` at the shifted torsion point; this gives holomorphy in `τ`.
* Boundedness at `i∞` from the label-dependent lower bound for `θ₀` and uniform bounds for
  `θ₁, θ₂`; every cusp is reached through the covariance.

No statement of Eisenstein membership, Fourier expansion or spanning is made.
-/

noncomputable section

open Complex Filter Topology ModularGroup
open scoped Real UpperHalfPlane MatrixGroups ModularForm Manifold

namespace ZInQ.Contrib.HeckePrimeRationality.WeierstrassForms

open CompletedTheta ThetaWeierstrass TorsionWeierstrassData
open CongruenceSubgroup Matrix.SpecialLinearGroup
open ThetaFiveTorsion (act act_mul act_one act_S act_T)
open WeierstrassDistributionNat (G notMem_iff_H_ne_zero xValue_shift)
open ThetaG2 (th Ek)

variable {N : ℕ}

theorem xValue_bad {a b : ℤ} (h : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) (τ : ℍ) : xValue N a b τ = 0 := by
  simp [xValue, h]

/-! ### Transformation of `℘` -/

theorem wp_T (τ : ℍ) {z : ℂ} (hz : z ∉ (periodPair τ).lattice) :
    (periodPair (T • τ)).weierstrassP z = (periodPair τ).weierstrassP z := by
  have hz' : z ∉ (periodPair (T • τ)).lattice := by
    rw [notMem_iff_H_ne_zero, ThetaG2.H_T]; exact (notMem_iff_H_ne_zero τ z).mp hz
  rw [weierstrassP_eq_neg_deriv_logDerivative _ z hz', weierstrassP_eq_neg_deriv_logDerivative _ z hz,
    ThetaG2.H_T, ThetaG2.finitePart_T]

theorem wp_S (τ : ℍ) {z : ℂ} (hz : (τ : ℂ) * z ∉ (periodPair τ).lattice) :
    (periodPair (S • τ)).weierstrassP z = (τ : ℂ) ^ 2 * (periodPair τ).weierstrassP ((τ : ℂ) * z) := by
  have hH : H τ ((τ : ℂ) * z) ≠ 0 := (notMem_iff_H_ne_zero τ _).mp hz
  have hz' : z ∉ (periodPair (S • τ)).lattice := by
    rw [notMem_iff_H_ne_zero, ThetaG2.H_S]; exact mul_ne_zero (ThetaG2.g_ne_zero τ z) hH
  have e1 := weierstrassP_eq_neg_deriv_logDerivative (S • τ) z hz'
  have e2 := weierstrassP_eq_neg_deriv_logDerivative τ _ hz
  change _ = -deriv (G (S • τ)) z + finitePart (S • τ) at e1
  change _ = -deriv (G τ) ((τ : ℂ) * z) + finitePart τ at e2
  rw [e1, e2, ThetaG2.deriv_G_S τ hH, ThetaG2.finitePart_S]
  ring

theorem tp_T (N : ℕ) (a b : ℤ) (τ : ℍ) :
    torsionPoint N a b (T • τ) = torsionPoint N a (a + b) τ := by
  unfold torsionPoint; rw [ThetaFive.coe_T_smul]; push_cast; ring

theorem tp_S (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    (τ : ℂ) * torsionPoint N a b (S • τ) = torsionPoint N b (-a) τ := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold torsionPoint; rw [ThetaFive.coe_S_smul]; push_cast; field_simp; ring

theorem tp_notMem (hN : 0 < N) {a b : ℤ} (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) (τ : ℍ) :
    torsionPoint N a b τ ∉ (periodPair τ).lattice := by
  rw [notMem_iff_H_ne_zero]; exact H_torsion_ne_zero N hN τ a b hg

theorem xValue_T (hN : 0 < N) (a b : ℤ) (τ : ℍ) : xValue N a b (T • τ) = xValue N a (a + b) τ := by
  by_cases hg : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · rw [xValue_bad hg, xValue_bad ⟨hg.1, dvd_add hg.1 hg.2⟩]
  · have hg' : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ a + b) := fun h => hg ⟨h.1, (dvd_add_right h.1).mp h.2⟩
    rw [xValue_of_good _ _ _ _ hg, xValue_of_good _ _ _ _ hg', tp_T]
    exact wp_T τ (tp_notMem hN hg' τ)

theorem xValue_S (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    xValue N a b (S • τ) = (τ : ℂ) ^ 2 * xValue N b (-a) τ := by
  by_cases hg : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · rw [xValue_bad hg, xValue_bad ⟨hg.2, (dvd_neg).mpr hg.1⟩, mul_zero]
  · have hg' : ¬ ((N : ℤ) ∣ b ∧ (N : ℤ) ∣ -a) := fun h => hg ⟨(dvd_neg).mp h.2, h.1⟩
    rw [xValue_of_good _ _ _ _ hg, xValue_of_good _ _ _ _ hg', ← tp_S hN a b τ]
    apply wp_S
    rw [tp_S hN]; exact tp_notMem hN hg' τ

/-! ### Covariance -/

/-- The family of weight-two functions. -/
def X (N : ℕ) (v : ℤ × ℤ) : ℍ → ℂ := fun τ => xValue N v.1 v.2 τ

theorem X_slash_S (hN : 0 < N) (v : ℤ × ℤ) : X N v ∣[(2 : ℤ)] S = X N (act v S) := by
  obtain ⟨a, b⟩ := v
  funext τ
  rw [ModularForm.SL_slash_apply, act_S, ModularGroup.denom_S]
  simp only [X]
  rw [xValue_S hN, zpow_neg, zpow_two]
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  field_simp

theorem X_slash_T (hN : 0 < N) (v : ℤ × ℤ) : X N v ∣[(2 : ℤ)] T = X N (act v T) := by
  obtain ⟨a, b⟩ := v
  funext τ
  have hd : UpperHalfPlane.denom T τ = 1 := by
    rw [ModularGroup.denom_apply]; simp [ModularGroup.coe_T]
  rw [ModularForm.SL_slash_apply, act_T, hd, one_zpow, mul_one]
  simp only [X]
  exact xValue_T hN a b τ

/-- **Covariance**: `x_v ∣[2] γ = x_{v γ}` for all `γ ∈ SL(2, ℤ)` and all labels `v`. -/
theorem X_slash (hN : 0 < N) (γ : SL(2, ℤ)) : ∀ v : ℤ × ℤ, X N v ∣[(2 : ℤ)] γ = X N (act v γ) := by
  have hg : γ ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact fun v => X_slash_S hN v
    · exact fun v => X_slash_T hN v
  | one =>
    intro v
    rw [SlashAction.slash_one, act_one]
  | mul x y _ _ hx hy =>
    intro v
    rw [SlashAction.slash_mul, hx v, hy, act_mul]
  | inv x _ hx =>
    intro v
    have h1 := hx (act v x⁻¹)
    rw [act_mul, inv_mul_cancel, act_one] at h1
    rw [← h1, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

theorem X_slash_Gamma (hN : 0 < N) (v : ℤ × ℤ) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    X N v ∣[(2 : ℤ)] γ = X N v := by
  rw [X_slash hN γ v]
  obtain ⟨⟨m, hm⟩, ⟨k, hk⟩⟩ := AllLevelPrincipal.congr_act_Gamma hγ v
  have he : act v γ = (v.1 + N * m, v.2 + N * k) :=
    Prod.ext (by dsimp only; linarith) (by dsimp only; linarith)
  funext τ
  simp only [X]
  rw [he]
  exact xValue_shift hN _ _ m k τ

/-! ### Explicit theta form and holomorphy -/

theorem deriv_G_eq (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) :
    deriv (G τ) z = (Ek τ 2 z * Ek τ 0 z - Ek τ 1 z ^ 2) / Ek τ 0 z ^ 2 := by
  have hderiv : ∀ x, deriv (H τ) x = π * I * Ek τ 0 x + Ek τ 1 x := fun x => by
    rw [ThetaG2.H_eq_E0, (ThetaG2.hasDerivAt_Ek τ 0 x).deriv]
  have hG : G τ = fun x => (π * I * Ek τ 0 x + Ek τ 1 x) / Ek τ 0 x := by
    funext x
    show deriv (H τ) x / H τ x = _
    rw [hderiv, ThetaG2.H_eq_E0]
  have h0 : Ek τ 0 z ≠ 0 := by rw [← ThetaG2.H_eq_E0]; exact hz
  have hd := (((ThetaG2.hasDerivAt_Ek τ 0 z).const_mul (π * I)).add
    (ThetaG2.hasDerivAt_Ek τ 1 z)).div (ThetaG2.hasDerivAt_Ek τ 0 z) h0
  have hfun : (fun x => (π * I * Ek τ 0 x + Ek τ 1 x) / Ek τ 0 x) =
      ((fun y => π * I * Ek τ 0 y) + Ek τ 1) / Ek τ 0 := by
    funext x; simp
  rw [hG, hfun, hd.deriv]
  simp only [Pi.add_apply]
  field_simp
  ring

theorem wp_eq_th (τ : ℍ) {z : ℂ} (hz : z ∉ (periodPair τ).lattice) :
    (periodPair τ).weierstrassP z =
      (th 1 (z + ((τ : ℂ) + 1) / 2) τ ^ 2 -
          th 2 (z + ((τ : ℂ) + 1) / 2) τ * th 0 (z + ((τ : ℂ) + 1) / 2) τ) /
        th 0 (z + ((τ : ℂ) + 1) / 2) τ ^ 2 + finitePart τ := by
  have hH := (notMem_iff_H_ne_zero τ z).mp hz
  have e := weierstrassP_eq_neg_deriv_logDerivative τ z hz
  change _ = -deriv (G τ) z + finitePart τ at e
  rw [e, deriv_G_eq τ hH]
  have h0 : Ek τ 0 z ≠ 0 := by rw [← ThetaG2.H_eq_E0]; exact hH
  simp only [ThetaG2.Ek] at h0 ⊢
  have he := Complex.exp_ne_zero (π * I * z)
  have hθ : th 0 (z + ((τ : ℂ) + 1) / 2) τ ≠ 0 := fun h => h0 (by rw [h, mul_zero])
  generalize th 0 (z + ((τ : ℂ) + 1) / 2) τ = A at hθ ⊢
  generalize th 1 (z + ((τ : ℂ) + 1) / 2) τ = B
  generalize th 2 (z + ((τ : ℂ) + 1) / 2) τ = C
  generalize cexp (π * I * z) = E at he ⊢
  field_simp
  ring

theorem xValue_eq_th (hN : 0 < N) (a b : ℤ) (τ : ℍ) (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    xValue N a b τ =
      (th 1 (Torsion.shiftedPoint N a b τ) τ ^ 2 -
          th 2 (Torsion.shiftedPoint N a b τ) τ * th 0 (Torsion.shiftedPoint N a b τ) τ) /
        th 0 (Torsion.shiftedPoint N a b τ) τ ^ 2 + finitePart τ := by
  rw [xValue_of_good _ _ _ _ hg, wp_eq_th τ (tp_notMem hN hg τ)]
  rfl

theorem differentiableAt_th_zc (k : ℕ) (a b : ℤ) {t : ℂ} (ht : 0 < t.im) :
    DifferentiableAt ℂ (fun u => th k (AllLevelForms.zc N a b u) u) t := by
  set T₀ := t.im / 2 with hT₀
  set T₁ := t.im + 1 with hT₁
  set S₀ := (|(a : ℝ) / N| + 1 / 2) * T₁ with hS₀
  set U := {u : ℂ | T₀ < u.im ∧ u.im < T₁} with hUdef
  have hT : 0 < T₀ := by positivity
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have htU : t ∈ U := ⟨by rw [hT₀]; linarith, by rw [hT₁]; linarith⟩
  have hD : DifferentiableOn ℂ (fun u => ∑' n : ℤ, (2 * π * I * n : ℂ) ^ k *
      jacobiTheta₂_term n (AllLevelForms.zc N a b u) u) U := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_pow_mul_jacobiTheta₂_term_bound S₀ hT k).mul_left ((2 * π) ^ k)) ?_ hU ?_
    · intro n
      refine Differentiable.differentiableOn ?_
      unfold jacobiTheta₂_term AllLevelForms.zc
      fun_prop
    · intro n u hu
      have hz : |(AllLevelForms.zc N a b u).im| ≤ S₀ := by
        rw [AllLevelForms.zc_im, abs_mul]
        have h1 : |((a : ℝ) / N + 1 / 2)| ≤ |(a : ℝ) / N| + 1 / 2 := by
          calc |((a : ℝ) / N + 1 / 2)| ≤ |(a : ℝ) / N| + |(1 : ℝ) / 2| := abs_add_le _ _
            _ = |(a : ℝ) / N| + 1 / 2 := by norm_num
        have h2 : |u.im| ≤ T₁ := by
          rw [abs_of_pos (by linarith [hu.1])]; exact hu.2.le
        exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      exact ThetaG2.norm_term_coeff_le k hT hz hu.1.le n
  exact hD.differentiableAt (hU.mem_nhds htU)

theorem X_diffOn (hN : 0 < N) {a b : ℤ} (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    DifferentiableOn ℂ (X N (a, b) ∘ UpperHalfPlane.ofComplex) {z | 0 < z.im} := by
  have hq : DifferentiableOn ℂ (fun t : ℂ =>
      (th 1 (AllLevelForms.zc N a b t) t ^ 2 -
          th 2 (AllLevelForms.zc N a b t) t * th 0 (AllLevelForms.zc N a b t) t) /
        th 0 (AllLevelForms.zc N a b t) t ^ 2) {z | 0 < z.im} := by
    intro t ht
    have h0 : th 0 (AllLevelForms.zc N a b t) t ≠ 0 := by
      rw [ThetaG2.th_zero]
      exact AllLevelTheta.jacobiTheta₂_shiftedPoint_ne_zero N hN ⟨t, ht⟩ a b hg
    have d0 := differentiableAt_th_zc (N := N) 0 a b ht
    have d1 := differentiableAt_th_zc (N := N) 1 a b ht
    have d2 := differentiableAt_th_zc (N := N) 2 a b ht
    exact (((d1.pow 2).sub (d2.mul d0)).div (d0.pow 2) (pow_ne_zero 2 h0)).differentiableWithinAt
  have hsum := hq.add ThetaG2.finitePart_diffOn
  refine hsum.congr fun t ht => ?_
  simp only [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos ht, X]
  rw [xValue_eq_th hN a b ⟨t, ht⟩ hg]
  simp only [Pi.add_apply, Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos ht]
  rfl

theorem X_mdiff (hN : 0 < N) (v : ℤ × ℤ) : MDiff (X N v) := by
  obtain ⟨a, b⟩ := v
  by_cases hg : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · have h0 : X N (a, b) = fun _ => 0 := funext fun τ => xValue_bad hg τ
    rw [h0]
    exact fun _ => mdifferentiableAt_const
  · exact UpperHalfPlane.mdifferentiable_iff.mpr (X_diffOn hN hg)

/-! ### Boundedness -/

theorem norm_th_le (k : ℕ) {z τ : ℂ} (hy : 1 ≤ τ.im) (hz : |z.im| ≤ τ.im / 2) :
    ‖th k z τ‖ ≤ ThetaG2.B k := by
  have hy0 : 0 < τ.im := by linarith
  have hle : ∀ n : ℤ, ‖(2 * π * I * n : ℂ) ^ k * jacobiTheta₂_term n z τ‖ ≤
      (2 * π) ^ k * (((|n| : ℤ) : ℝ) ^ k *
        Real.exp (-π * (1 * n ^ 2 - 2 * (1 / 2) * ((|n| : ℤ) : ℝ)))) := by
    intro n
    refine (ThetaG2.norm_term_coeff_le k hy0 hz le_rfl n).trans ?_
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
      (by positivity)) (by positivity)
    have hn : ((|n| : ℤ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h0 : |n| ≤ n ^ 2 := by
        have := Int.natAbs_le_self_sq n
        rwa [Int.natCast_natAbs] at this
      exact_mod_cast h0
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy (sub_nonneg.mpr hn))
      Real.pi_pos.le]
  have hs : Summable fun n : ℤ => ‖(2 * π * I * n : ℂ) ^ k * jacobiTheta₂_term n z τ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle (ThetaG2.summable_B k)
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_mono (ThetaG2.summable_B k) hle)

theorem slope_le (hN : 0 < N) {a b : ℤ}
    (hrep : (1 - (N : ℤ) ≤ a ∧ a ≤ -1) ∨ (a = 0 ∧ ¬ (N : ℤ) ∣ b)) (τ : ℍ) :
    |(Torsion.shiftedPoint N a b τ).im| ≤ (τ : ℂ).im / 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hy : 0 < (τ : ℂ).im := τ.im_pos
  have him : (Torsion.shiftedPoint N a b τ).im = ((a : ℝ) / N + 1 / 2) * (τ : ℂ).im :=
    AllLevelForms.zc_im N a b τ
  rw [him, abs_mul, abs_of_pos hy]
  have : |(a : ℝ) / N + 1 / 2| ≤ 1 / 2 := by
    rcases hrep with ⟨ha1, ha2⟩ | ⟨rfl, _⟩
    · have ha1' : (1 : ℝ) - N ≤ a := by exact_mod_cast ha1
      have ha2' : (a : ℝ) ≤ -1 := by exact_mod_cast ha2
      rw [abs_le, show (a : ℝ) / N = a * (1 / N) by ring]
      have hinv : (1 / (N : ℝ)) * N = 1 := by field_simp
      constructor <;> nlinarith [one_div_pos.mpr hNr]
    · norm_num
  nlinarith

theorem good_of_rep {a b : ℤ}
    (hrep : (1 - (N : ℤ) ≤ a ∧ a ≤ -1) ∨ (a = 0 ∧ ¬ (N : ℤ) ∣ b)) :
    ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) := by
  rcases hrep with ⟨h1, h2⟩ | ⟨rfl, hb⟩
  · rintro ⟨⟨k, hk⟩, _⟩
    rw [hk] at h1 h2
    have hk1 : k < 0 := by
      by_contra hk0
      push Not at hk0
      nlinarith
    have hk2 : -1 < k := by
      by_contra hk0
      push Not at hk0
      nlinarith
    omega
  · exact fun h => hb h.2

theorem xValue_bounded_rep (hN : 0 < N) {a b : ℤ}
    (hrep : (1 - (N : ℤ) ≤ a ∧ a ≤ -1) ∨ (a = 0 ∧ ¬ (N : ℤ) ∣ b)) :
    ∃ M A : ℝ, ∀ τ : ℍ, A ≤ τ.im → ‖xValue N a b τ‖ ≤ M := by
  obtain ⟨c, hc, A, hA1, hlow⟩ := AllLevelForms.exists_theta_lower hN hrep
  obtain ⟨Mf, Af, hf⟩ := ThetaG2.finitePart_bounded
  have hg := good_of_rep hrep
  refine ⟨(ThetaG2.B 1 ^ 2 + ThetaG2.B 2 * ThetaG2.B 0) / c ^ 2 + Mf, max A Af, fun τ hτ => ?_⟩
  have hτA : A ≤ (τ : ℂ).im := le_trans (le_max_left _ _) hτ
  have hy1 : 1 ≤ (τ : ℂ).im := le_trans hA1 hτA
  have hz := slope_le hN hrep τ
  have h0 := hlow τ hτA
  rw [← ThetaG2.th_zero] at h0
  rw [xValue_eq_th hN a b τ hg]
  set s := Torsion.shiftedPoint N a b τ
  have b0 := norm_th_le 0 hy1 hz
  have b1 := norm_th_le 1 hy1 hz
  have b2 := norm_th_le 2 hy1 hz
  have hB0 : 0 ≤ ThetaG2.B 0 := le_trans (norm_nonneg _) b0
  have hB1 : 0 ≤ ThetaG2.B 1 := le_trans (norm_nonneg _) b1
  have hB2 : 0 ≤ ThetaG2.B 2 := le_trans (norm_nonneg _) b2
  have hnum : ‖th 1 s τ ^ 2 - th 2 s τ * th 0 s τ‖ ≤ ThetaG2.B 1 ^ 2 + ThetaG2.B 2 * ThetaG2.B 0 := by
    calc ‖th 1 s τ ^ 2 - th 2 s τ * th 0 s τ‖ ≤ ‖th 1 s τ‖ ^ 2 + ‖th 2 s τ‖ * ‖th 0 s τ‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_pow, norm_mul]
      _ ≤ ThetaG2.B 1 ^ 2 + ThetaG2.B 2 * ThetaG2.B 0 := by
          gcongr
  have hden : c ^ 2 ≤ ‖th 0 s τ ^ 2‖ := by
    rw [norm_pow]; gcongr
  have hq : ‖(th 1 s τ ^ 2 - th 2 s τ * th 0 s τ) / th 0 s τ ^ 2‖ ≤
      (ThetaG2.B 1 ^ 2 + ThetaG2.B 2 * ThetaG2.B 0) / c ^ 2 := by
    rw [norm_div]
    calc ‖th 1 s τ ^ 2 - th 2 s τ * th 0 s τ‖ / ‖th 0 s τ ^ 2‖
        ≤ (ThetaG2.B 1 ^ 2 + ThetaG2.B 2 * ThetaG2.B 0) / ‖th 0 s τ ^ 2‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ (ThetaG2.B 1 ^ 2 + ThetaG2.B 2 * ThetaG2.B 0) / c ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hfp := hf τ (le_trans (le_max_right _ _) hτ)
  calc ‖(th 1 s τ ^ 2 - th 2 s τ * th 0 s τ) / th 0 s τ ^ 2 + finitePart τ‖
      ≤ ‖(th 1 s τ ^ 2 - th 2 s τ * th 0 s τ) / th 0 s τ ^ 2‖ + ‖finitePart τ‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hq hfp

/-- Every label's function is bounded at `i∞`. -/
theorem X_isBoundedAtImInfty (hN : 0 < N) (v : ℤ × ℤ) :
    UpperHalfPlane.IsBoundedAtImInfty (X N v) := by
  obtain ⟨a, b⟩ := v
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  have hqr := Int.mul_ediv_add_emod a N
  have hr0 := Int.emod_nonneg a hNz.ne'
  have hr1 := Int.emod_lt_of_pos a hNz
  by_cases ha : a % N = 0
  · have he : ∀ τ, X N (a, b) τ = xValue N 0 b τ := fun τ => by
      have h := xValue_shift hN 0 b (a / N) 0 τ
      rwa [show (0 : ℤ) + N * (a / N) = a by rw [ha] at hqr; linarith,
        show b + (N : ℤ) * 0 = b by ring] at h
    by_cases hb : (N : ℤ) ∣ b
    · exact ⟨0, 0, fun τ _ => by rw [he, xValue_bad ⟨dvd_zero _, hb⟩, norm_zero]⟩
    · obtain ⟨M, A, hMA⟩ := xValue_bounded_rep hN (a := 0) (b := b) (Or.inr ⟨rfl, hb⟩)
      exact ⟨M, A, fun τ hτ => by rw [he]; exact hMA τ hτ⟩
  · have hrep : 1 - (N : ℤ) ≤ a % N - N ∧ a % N - N ≤ -1 := by
      constructor
      · have : 0 < a % N := lt_of_le_of_ne hr0 (Ne.symm ha)
        linarith
      · linarith
    have he : ∀ τ, X N (a, b) τ = xValue N (a % N - N) b τ := fun τ => by
      have h := xValue_shift hN (a % N - N) b (a / N + 1) 0 τ
      rwa [show a % N - N + (N : ℤ) * (a / N + 1) = a by linarith,
        show b + (N : ℤ) * 0 = b by ring] at h
    obtain ⟨M, A, hMA⟩ := xValue_bounded_rep hN (Or.inl hrep)
    exact ⟨M, A, fun τ hτ => by rw [he]; exact hMA τ hτ⟩

theorem X_bdd_cusp (hN : 0 < N) (v : ℤ × ℤ) {c : OnePoint ℝ}
    (hc : IsCusp c ((CongruenceSubgroup.Gamma N).map (mapGL ℝ))) : c.IsBoundedAt (X N v) 2 := by
  have hc' : IsCusp c 𝒮ℒ := IsCusp.mono (Subgroup.map_le_range _ _) hc
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
  intro γ _
  rw [X_slash hN γ v]
  exact X_isBoundedAtImInfty hN _

/-! ### The modular forms -/

/-- **The weight-two form on `Γ(N)` with values `xValue N a b`**, for all integers `a, b`. -/
def xForm (N : ℕ) (hN : 0 < N) (a b : ℤ) : ModularForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) 2 where
  toFun := X N (a, b)
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    have := X_slash_Gamma hN (a, b) g hg
    rwa [ModularForm.SL_slash] at this
  holo' := X_mdiff hN (a, b)
  bdd_at_cusps' hc := X_bdd_cusp hN (a, b) hc

theorem xForm_apply (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    xForm N hN a b τ = xValue N a b τ := rfl

open Classical in
/-- The weight-one form on `Γ(N)` with values `lambdaValue N a b`. -/
def lambdaForm (N : ℕ) (hN : 0 < N) (a b : ℤ) : ModularForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) 1 :=
  if h : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b then 0 else scale • AllLevelPrincipal.principalForm N hN a b h

theorem lambdaForm_apply (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    lambdaForm N hN a b τ = lambdaValue N a b τ := by
  unfold lambdaForm
  split_ifs with h
  · simp [lambdaValue, TorsionDistributionTwo.reg_of_bad h]
  · rw [lambdaValue_of_good N a b τ h]
    rfl

/-- The weight-two form on `Γ(N)` with values `muValue N a b = (lambdaValue² - xValue)/2`. -/
def muForm (N : ℕ) (hN : 0 < N) (a b : ℤ) : ModularForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) 2 :=
  (1 / 2 : ℂ) • (ModularForm.mcast (by norm_num)
    ((lambdaForm N hN a b).mul (lambdaForm N hN a b)) - xForm N hN a b)

theorem muForm_apply (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    muForm N hN a b τ = muValue N a b τ := by
  show (1 / 2 : ℂ) * (lambdaForm N hN a b τ * lambdaForm N hN a b τ - xForm N hN a b τ) = _
  rw [lambdaForm_apply, xForm_apply, muValue]
  ring

end ZInQ.Contrib.HeckePrimeRationality.WeierstrassForms
