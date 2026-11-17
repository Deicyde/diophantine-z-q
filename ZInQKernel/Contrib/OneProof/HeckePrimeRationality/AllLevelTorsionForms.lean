import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaNonvanishing
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveTorsionForms

/-!
# Weight-one modular forms on `Γ₁(N)` from torsion theta quotients, for every level

For a positive level `N` and integers `a, b` not both divisible by `N`, let
`F_{a,b}(τ) = a/N + 1/2 + θ'(z, τ) / (2π i θ(z, τ))`, `z = (a τ + b)/N + (τ + 1)/2`,
with `θ = jacobiTheta₂` and `θ' = jacobiTheta₂'`; this is `Torsion.torsionLogDerivative N a b`.
The denominator never vanishes by the all-level nonvanishing theorem.

Main results.
* `F_T`, `F_S`, `F_shift`, `F_slash`: `F_{a,b}(τ + 1) = F_{a,a+b}(τ)`,
  `F_{a,b}(-1/τ) = τ F_{b,-a}(τ)`, dependence only on `(a, b)` modulo `N`, and
  `F_v ∣[1] γ = F_{v γ}` for all `γ ∈ SL(2, ℤ)`.
* Holomorphy on `ℍ`, and boundedness at `i∞` of every admissible `F_v`. The bounds depend on
  `N` and on the residue label: for `N ∤ a` a single dominant term with decay rate `2π/N`; for
  `N ∣ a` two dominant terms with limit `1 - exp(-2π i b/N) ≠ 0`.
* `torsionForm N hN b hb : ModularForm ((Gamma1 N).map (mapGL ℝ)) 1` with underlying function
  `torsionLogDerivative N 0 b`, for `¬ N ∣ b`.

No statement about nonvanishing of the resulting form, Fourier coefficients, dimensions, bases or
rationality is made.
-/

noncomputable section

open Complex ModularGroup
open scoped Real UpperHalfPlane MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelForms

open Torsion
open ThetaFiveTorsion (logDer act act_mul act_one act_S act_T logDer_add_int_left
  logDer_add_one_right logDer_add_tau theta_S_ne_zero logDer_S norm_theta'_le Kθ norm_two_pi_I)

variable {N : ℕ}

/-! ### The family and its laws -/

/-- Admissible index pairs at level `N`. -/
def Good (N : ℕ) (v : ℤ × ℤ) : Prop := ¬ ((N : ℤ) ∣ v.1 ∧ (N : ℤ) ∣ v.2)

/-- The family `F_{a,b} = torsionLogDerivative N a b`. -/
def F (N : ℕ) (v : ℤ × ℤ) : ℍ → ℂ := fun τ => torsionLogDerivative N v.1 v.2 τ

theorem F_apply (a b : ℤ) (τ : ℍ) :
    F N (a, b) τ = (a : ℂ) / N + 1 / 2 + logDer (shiftedPoint N a b τ) τ := rfl

theorem theta_ne_zero (hN : 0 < N) {a b : ℤ} (h : Good N (a, b)) (τ : ℍ) :
    jacobiTheta₂ (shiftedPoint N a b τ) τ ≠ 0 :=
  AllLevelTheta.jacobiTheta₂_shiftedPoint_ne_zero N hN τ a b h

theorem F_add_fst (hN : 0 < N) {a b : ℤ} (h : Good N (a, b)) (τ : ℍ) :
    F N (a + N, b) τ = F N (a, b) τ := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [F_apply, F_apply]
  have hz : shiftedPoint N (a + N) b τ = shiftedPoint N a b τ + τ := by
    unfold shiftedPoint; push_cast; field_simp; ring
  rw [hz, logDer_add_tau (theta_ne_zero hN h τ)]
  push_cast; field_simp; ring

theorem F_add_snd (hN : 0 < N) (a b : ℤ) (τ : ℍ) : F N (a, b + N) τ = F N (a, b) τ := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [F_apply, F_apply]
  have hz : shiftedPoint N a (b + N) τ = shiftedPoint N a b τ + ((1 : ℤ) : ℂ) := by
    unfold shiftedPoint; push_cast; field_simp; ring
  rw [hz, logDer_add_int_left]

theorem good_shift {a b : ℤ} (m n : ℤ) : Good N (a + N * m, b + N * n) ↔ Good N (a, b) := by
  unfold Good
  simp only
  rw [dvd_add_left (dvd_mul_right (N : ℤ) m), dvd_add_left (dvd_mul_right (N : ℤ) n)]

/-- `F_v` depends only on `v` modulo `N`. -/
theorem F_shift (hN : 0 < N) {a b : ℤ} (h : Good N (a, b)) (m n : ℤ) (τ : ℍ) :
    F N (a + N * m, b + N * n) τ = F N (a, b) τ := by
  have hsnd : ∀ a' b' : ℤ, ∀ n : ℤ, F N (a', b' + N * n) τ = F N (a', b') τ := by
    intro a' b' n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [show b' + N * ((k : ℤ) + 1) = (b' + N * k) + N by ring, F_add_snd hN, ih]
    | pred k ih =>
      rw [← ih, show b' + N * (-(k : ℤ)) = (b' + N * (-(k : ℤ) - 1)) + N by ring, F_add_snd hN]
  have hfst : ∀ m : ℤ, F N (a + N * m, b) τ = F N (a, b) τ := by
    intro m
    induction m using Int.induction_on with
    | zero => simp
    | succ k ih =>
      have hg : Good N (a + N * k, b) := by
        have := (good_shift (N := N) (a := a) (b := b) k 0).mpr h
        simpa using this
      rw [show a + N * ((k : ℤ) + 1) = (a + N * k) + N by ring, F_add_fst hN hg, ih]
    | pred k ih =>
      have hg : Good N (a + N * (-(k : ℤ) - 1), b) := by
        have := (good_shift (N := N) (a := a) (b := b) (-(k : ℤ) - 1) 0).mpr h
        simpa using this
      rw [← ih, show a + N * (-(k : ℤ)) = (a + N * (-(k : ℤ) - 1)) + N by ring,
        F_add_fst hN hg]
  rw [hsnd, hfst]

/-- The `T` law. -/
theorem F_T (hN : 0 < N) (a b : ℤ) (τ : ℍ) : F N (a, b) (T • τ) = F N (a, a + b) τ := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [F_apply, F_apply]
  have h1 : shiftedPoint N a b (T • τ) =
      ((a : ℂ) * ((τ : ℂ) + 1) + b) / N + ((τ : ℂ) + 1 + 1) / 2 := by
    unfold shiftedPoint; rw [ThetaFive.coe_T_smul]
  rw [h1, ThetaFive.coe_T_smul, logDer_add_one_right]
  have h2 : ((a : ℂ) * ((τ : ℂ) + 1) + b) / N + ((τ : ℂ) + 1 + 1) / 2 + 1 / 2 =
      shiftedPoint N a (a + b) τ + ((1 : ℤ) : ℂ) := by
    unfold shiftedPoint; push_cast; field_simp; ring
  rw [h2, logDer_add_int_left]

/-- The `S` law. -/
theorem F_S (hN : 0 < N) {a b : ℤ} (h : Good N (b, -a)) (τ : ℍ) :
    F N (a, b) (S • τ) = (τ : ℂ) * F N (b, -a) τ := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hθ := theta_ne_zero hN h τ
  rw [F_apply, F_apply]
  have h1 : shiftedPoint N a b (S • τ) = shiftedPoint N b (-a) τ / τ + (-1 / (τ : ℂ)) := by
    unfold shiftedPoint; rw [ThetaFive.coe_S_smul]; push_cast; field_simp; ring
  rw [h1, ThetaFive.coe_S_smul, logDer_add_tau (theta_S_ne_zero hθ), logDer_S hτ hθ]
  unfold shiftedPoint
  push_cast
  field_simp
  ring

theorem good_act {v : ℤ × ℤ} (h : Good N v) (γ : SL(2, ℤ)) : Good N (act v γ) := by
  rintro ⟨h1, h2⟩
  apply h
  have hv : act (act v γ) γ⁻¹ = v := by rw [act_mul, mul_inv_cancel, act_one]
  rw [← hv]
  set w := act v γ
  exact ⟨dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _),
    dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _)⟩

theorem F_slash_S (hN : 0 < N) {v : ℤ × ℤ} (h : Good N v) : F N v ∣[(1 : ℤ)] S = F N (act v S) := by
  obtain ⟨a, b⟩ := v
  have hg : Good N (b, -a) := by
    have := good_act h S
    rwa [act_S] at this
  funext τ
  rw [ModularForm.SL_slash_apply, act_S, F_S hN hg τ, ModularGroup.denom_S, zpow_neg_one]
  field_simp [τ.ne_zero]

theorem F_slash_T (hN : 0 < N) {v : ℤ × ℤ} (_h : Good N v) : F N v ∣[(1 : ℤ)] T = F N (act v T) := by
  obtain ⟨a, b⟩ := v
  funext τ
  have hd : UpperHalfPlane.denom T τ = 1 := by
    rw [ModularGroup.denom_apply]; simp [ModularGroup.coe_T]
  rw [ModularForm.SL_slash_apply, act_T, F_T hN, hd]
  simp

/-- **Covariance**: `F_v ∣[1] γ = F_{v γ}` for all `γ ∈ SL(2, ℤ)`. -/
theorem F_slash (hN : 0 < N) (γ : SL(2, ℤ)) :
    ∀ v : ℤ × ℤ, Good N v → F N v ∣[(1 : ℤ)] γ = F N (act v γ) := by
  have hg : γ ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact fun v hv => F_slash_S hN hv
    · exact fun v hv => F_slash_T hN hv
  | one =>
    intro v _
    rw [SlashAction.slash_one, act_one]
  | mul x y _ _ hx hy =>
    intro v hv
    rw [SlashAction.slash_mul, hx v hv, hy _ (good_act hv x), act_mul]
  | inv x _ hx =>
    intro v hv
    have hw := good_act hv x⁻¹
    have h1 := hx (act v x⁻¹) hw
    rw [act_mul, inv_mul_cancel, act_one] at h1
    rw [← h1, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

/-! ### Holomorphy -/

/-- The torsion point as a function on `ℂ`. -/
def zc (N : ℕ) (a b : ℤ) (τ : ℂ) : ℂ := ((a : ℂ) * τ + b) / N + (τ + 1) / 2

theorem zc_im (N : ℕ) (a b : ℤ) (τ : ℂ) :
    (zc N a b τ).im = ((a : ℝ) / N + 1 / 2) * τ.im := by
  simp [zc, Complex.div_natCast_im]; ring

theorem differentiableAt_theta_zc (a b : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun t => jacobiTheta₂ (zc N a b t) t) τ := by
  have h1 : DifferentiableAt ℂ (fun t : ℂ => (zc N a b t, t)) τ := by
    refine DifferentiableAt.prodMk ?_ differentiableAt_id
    unfold zc; fun_prop
  exact DifferentiableAt.comp (f := fun t : ℂ => (zc N a b t, t))
    (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) τ
    (hasFDerivAt_jacobiTheta₂ (zc N a b τ) hτ).differentiableAt h1

theorem differentiableAt_theta'_zc (a b : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun t => jacobiTheta₂' (zc N a b t) t) τ := by
  set T₀ := τ.im / 2 with hT₀
  set T₁ := τ.im + 1 with hT₁
  set S₀ := (|(a : ℝ) / N| + 1 / 2) * T₁ with hS₀
  set U := {t : ℂ | T₀ < t.im ∧ t.im < T₁} with hUdef
  have hT : 0 < T₀ := by positivity
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have hτU : τ ∈ U := ⟨by rw [hT₀]; linarith, by rw [hT₁]; linarith⟩
  have hD : DifferentiableOn ℂ (fun t => ∑' n : ℤ, jacobiTheta₂'_term n (zc N a b t) t) U := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_pow_mul_jacobiTheta₂_term_bound S₀ hT 1).mul_left (2 * π)) ?_ hU ?_
    · intro n
      refine Differentiable.differentiableOn ?_
      unfold jacobiTheta₂'_term jacobiTheta₂_term zc
      fun_prop
    · intro n t ht
      have hz : |(zc N a b t).im| ≤ S₀ := by
        rw [zc_im, abs_mul]
        have h1 : |((a : ℝ) / N + 1 / 2)| ≤ |(a : ℝ) / N| + 1 / 2 := by
          calc |((a : ℝ) / N + 1 / 2)| ≤ |(a : ℝ) / N| + |(1 : ℝ) / 2| := abs_add_le _ _
            _ = |(a : ℝ) / N| + 1 / 2 := by norm_num
        have h2 : |t.im| ≤ T₁ := by
          rw [abs_of_pos (by linarith [ht.1])]; exact ht.2.le
        exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      refine (norm_jacobiTheta₂'_term_le hT hz ht.1.le n).trans (le_of_eq ?_)
      ring
  exact hD.differentiableAt (hU.mem_nhds hτU)

theorem F_diffOn (hN : 0 < N) {a b : ℤ} (h : Good N (a, b)) :
    DifferentiableOn ℂ (F N (a, b) ∘ UpperHalfPlane.ofComplex) {z | 0 < z.im} := by
  have hD : DifferentiableOn ℂ (fun t : ℂ => (a : ℂ) / N + 1 / 2 +
      jacobiTheta₂' (zc N a b t) t / (2 * (π : ℂ) * I * jacobiTheta₂ (zc N a b t) t))
      {z | 0 < z.im} := by
    intro t ht
    have hne : 2 * (π : ℂ) * I * jacobiTheta₂ (zc N a b t) t ≠ 0 :=
      mul_ne_zero ThetaFiveTorsion.two_pi_I_ne_zero (theta_ne_zero hN h ⟨t, ht⟩)
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (differentiableAt_const _).add ((differentiableAt_theta'_zc a b ht).div
      ((differentiableAt_const _).mul (differentiableAt_theta_zc a b ht)) hne)
  refine hD.congr fun t ht => ?_
  simp only [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos ht]
  rfl

/-! ### Boundedness at `i∞` -/

/-- One dominant term: if `|Im z| ≤ (1/2 - 1/N) Im τ` and `Im τ ≥ N`, then `‖θ(z, τ) - 1‖ ≤ 1/2`. -/
theorem norm_theta_sub_one_le (hN : 0 < N) {z τ : ℂ} (hyN : (N : ℝ) ≤ τ.im)
    (hz : |z.im| ≤ (1 / 2 - 1 / N) * τ.im) : ‖jacobiTheta₂ z τ - 1‖ ≤ 1 / 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hy : 0 < τ.im := by linarith
  set y := τ.im with hydef
  set ρ := Real.exp (-(2 * π * y / N)) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hyN' : 1 ≤ y / N := by rw [le_div_iff₀ hNr]; linarith
  have hρu : ρ ≤ Real.exp (-1) * Real.exp (-1) := by
    rw [hρ, ← Real.exp_add, Real.exp_le_exp]
    have : 2 * π * y / N = 2 * π * (y / N) := by ring
    rw [this]; nlinarith [Real.pi_gt_three]
  have hu := ThetaFive.exp_neg_one_lt
  have hu0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hρ1 : ρ < 1 := by nlinarith
  have hM := ThetaFive.hasSum_geom_natAbs 1 hρ0 hρ1
  have hf := hasSum_jacobiTheta₂_term z hy
  have hbound : ∀ n ∉ ({0} : Finset ℤ), ‖jacobiTheta₂_term n z τ‖ ≤ 1 * ρ ^ n.natAbs := by
    intro n hn
    simp only [Finset.mem_singleton] at hn
    rw [norm_jacobiTheta₂_term, one_mul, hρ, ← Real.exp_nat_mul, Real.exp_le_exp]
    set k : ℝ := ((n.natAbs : ℕ) : ℝ) with hkdef
    have hk : k = |(n : ℝ)| := by rw [hkdef, Nat.cast_natAbs, Int.cast_abs]
    have hk1 : 1 ≤ k := by
      rw [hkdef]; exact_mod_cast Int.natAbs_pos.mpr hn
    have hsq : (n : ℝ) ^ 2 = k ^ 2 := by rw [hk, sq_abs]
    have hlin : -(2 * (n : ℝ) * z.im) ≤ 2 * k * ((1 / 2 - 1 / N) * y) := by
      calc -(2 * (n : ℝ) * z.im) ≤ |2 * (n : ℝ) * z.im| := neg_le_abs _
        _ = 2 * k * |z.im| := by rw [abs_mul, abs_mul, hk]; norm_num
        _ ≤ 2 * k * ((1 / 2 - 1 / N) * y) :=
          mul_le_mul_of_nonneg_left hz (by positivity)
    have hR : k * -(2 * π * y / N) = -(2 * π * y * k * (1 / N)) := by ring
    rw [hR, ← hydef]
    have e1 := mul_le_mul_of_nonneg_left hlin Real.pi_pos.le
    have e2 : 0 ≤ π * y * (k * (k - 1)) :=
      mul_nonneg (mul_nonneg Real.pi_pos.le hy.le)
        (mul_nonneg (by linarith) (by linarith))
    have e3 : π * y * (n : ℝ) ^ 2 = π * y * k ^ 2 := by rw [hsq]
    nlinarith [e1, e2, e3]
  have key := ThetaFive.norm_tsum_sub_finset_le hf.summable hM.summable {0} hbound
  rw [hf.tsum_eq, hM.tsum_eq] at key
  simp only [Finset.sum_singleton, Int.natAbs_zero, pow_zero, one_mul] at key
  have h0term : jacobiTheta₂_term 0 z τ = 1 := by simp [jacobiTheta₂_term]
  rw [h0term] at key
  refine key.trans ?_
  have h1ρ : 0 < 1 - ρ := by linarith
  have : 1 / (1 - ρ) + ρ / (1 - ρ) - 1 = 2 * ρ / (1 - ρ) := by field_simp; ring
  rw [this, div_le_iff₀ h1ρ]
  nlinarith

/-- Two dominant terms: the tail of `θ(b/N + (τ+1)/2, τ)` beyond the indices `0, -1`. -/
theorem norm_theta_sub_dom_le {b : ℝ} {τ : ℂ} (hy1 : 1 ≤ τ.im) :
    ‖jacobiTheta₂ ((b : ℂ) + (τ + 1) / 2) τ - (1 + -Complex.exp (-(2 * π * I * b)))‖ ≤
      3 * Real.exp (-π * τ.im) := by
  have hy : 0 < τ.im := by linarith
  set z : ℂ := (b : ℂ) + (τ + 1) / 2 with hzdef
  set y := τ.im with hydef
  have hzim : z.im = y / 2 := by rw [hzdef]; simp [hydef]
  set ρ := Real.exp (-π * y) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hu := ThetaFive.exp_neg_one_lt
  have hu0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hρu : ρ ≤ Real.exp (-1) := by
    rw [hρ, Real.exp_le_exp]; nlinarith [Real.pi_gt_three]
  have hρ1 : ρ < 1 := by linarith
  have hM := ThetaFive.hasSum_geom_natAbs 1 hρ0 hρ1
  have hf := hasSum_jacobiTheta₂_term z hy
  have hbound : ∀ n ∉ ({0, -1} : Finset ℤ), ‖jacobiTheta₂_term n z τ‖ ≤ 1 * ρ ^ n.natAbs := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [norm_jacobiTheta₂_term, hzim, one_mul, hρ, ← Real.exp_nat_mul, Real.exp_le_exp]
    have hint : |n| ≤ n ^ 2 + n := by
      rcases le_or_gt 0 n with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_neg h]
        have : n ≤ -2 := by omega
        nlinarith
    have hreal : ((n.natAbs : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      rw [Nat.cast_natAbs]; exact_mod_cast hint
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hreal (mul_pos Real.pi_pos hy).le]
  have key := ThetaFive.norm_tsum_sub_finset_le hf.summable hM.summable {0, -1} hbound
  rw [hf.tsum_eq, hM.tsum_eq] at key
  rw [Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num)] at key
  simp only [Int.natAbs_zero, pow_zero, mul_one, one_mul, Int.natAbs_neg, Int.natAbs_one,
    pow_one] at key
  have h0term : jacobiTheta₂_term 0 z τ = 1 := by simp [jacobiTheta₂_term]
  have h1term : jacobiTheta₂_term (-1) z τ = -Complex.exp (-(2 * π * I * b)) := by
    simp only [jacobiTheta₂_term, hzdef]
    have : 2 * (π : ℂ) * I * ((-1 : ℤ) : ℂ) * ((b : ℂ) + (τ + 1) / 2) +
        π * I * ((-1 : ℤ) : ℂ) ^ 2 * τ = -(2 * π * I * b) + (π * I) * (-1 : ℤ) := by
      push_cast; ring
    rw [this, Complex.exp_add, mul_comm (π * I : ℂ), Complex.exp_int_mul,
      Complex.exp_pi_mul_I]
    norm_num
  rw [h0term, h1term] at key
  refine key.trans ?_
  have h1ρ : 0 < 1 - ρ := by linarith
  have : 1 / (1 - ρ) + ρ / (1 - ρ) - (1 + ρ) = ρ * (1 + ρ) / (1 - ρ) := by field_simp; ring
  rw [this, div_le_iff₀ h1ρ]
  nlinarith

/-- A lower bound for the denominator at `i∞`, depending on the residue label. -/
theorem exists_theta_lower (hN : 0 < N) {a b : ℤ}
    (hrep : (1 - (N : ℤ) ≤ a ∧ a ≤ -1) ∨ (a = 0 ∧ ¬ (N : ℤ) ∣ b)) :
    ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 1 ≤ A ∧ ∀ τ : ℍ, A ≤ τ.im →
      c ≤ ‖jacobiTheta₂ (shiftedPoint N a b τ) τ‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases hrep with ⟨ha1, ha2⟩ | ⟨rfl, hb⟩
  · refine ⟨1 / 2, by norm_num, N, hN1, fun τ hτ => ?_⟩
    have hyN : (N : ℝ) ≤ (τ : ℂ).im := hτ
    have hy : 0 < (τ : ℂ).im := τ.im_pos
    have hz : |(shiftedPoint N a b τ).im| ≤ (1 / 2 - 1 / N) * (τ : ℂ).im := by
      have him : (shiftedPoint N a b τ).im = ((a : ℝ) / N + 1 / 2) * (τ : ℂ).im :=
        zc_im N a b τ
      rw [him, abs_mul, abs_of_pos hy]
      refine mul_le_mul_of_nonneg_right ?_ hy.le
      have ha1' : (1 : ℝ) - N ≤ a := by exact_mod_cast ha1
      have ha2' : (a : ℝ) ≤ -1 := by exact_mod_cast ha2
      rw [abs_le]
      constructor
      · rw [show (a : ℝ) / N = a * (1 / N) by ring]
        have hinv : (1 / (N : ℝ)) * N = 1 := by field_simp
        nlinarith [one_div_pos.mpr hNr]
      · rw [show (a : ℝ) / N = a * (1 / N) by ring]
        nlinarith [one_div_pos.mpr hNr]
    have h := norm_theta_sub_one_le hN hyN hz
    have h2 := norm_sub_norm_le (1 : ℂ) (jacobiTheta₂ (shiftedPoint N a b τ) τ)
    rw [norm_sub_rev, norm_one] at h2
    linarith
  · set D : ℂ := 1 + -Complex.exp (-(2 * π * I * ((b : ℝ) / N : ℝ))) with hD
    have hD0 : D ≠ 0 := by
      intro h0
      have h1 : Complex.exp (-(2 * π * I * ((b : ℝ) / N : ℝ))) = 1 := by
        linear_combination -h0
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
      have h2 : (2 * π * I : ℂ) ≠ 0 := ThetaFiveTorsion.two_pi_I_ne_zero
      have h3 : -(((b : ℝ) / N : ℝ) : ℂ) = n := by
        apply mul_right_cancel₀ h2
        linear_combination hn
      have h4 := congrArg Complex.re h3
      simp at h4
      apply hb
      refine ⟨-n, ?_⟩
      have h5 : (b : ℝ) = N * (-n : ℤ) := by
        push_cast
        field_simp at h4
        linarith
      exact_mod_cast h5
    set δ := ‖D‖ with hδ
    have hδ0 : 0 < δ := norm_pos_iff.mpr hD0
    refine ⟨δ / 2, by positivity, max 1 (Real.log (6 / δ) / π), le_max_left _ _, fun τ hτ => ?_⟩
    have hy1 : 1 ≤ (τ : ℂ).im := le_trans (le_max_left _ _) hτ
    have hlog : Real.log (6 / δ) / π ≤ (τ : ℂ).im := le_trans (le_max_right _ _) hτ
    have e : shiftedPoint N 0 b τ = (((b : ℝ) / N : ℝ) : ℂ) + ((τ : ℂ) + 1) / 2 := by
      unfold shiftedPoint; push_cast; ring
    have htail := norm_theta_sub_dom_le (b := (b : ℝ) / N) hy1
    rw [← e] at htail
    have hsmall : 3 * Real.exp (-π * (τ : ℂ).im) ≤ δ / 2 := by
      have : -π * (τ : ℂ).im ≤ -Real.log (6 / δ) := by
        have := (div_le_iff₀ Real.pi_pos).mp hlog
        linarith
      have h6 : Real.exp (-π * (τ : ℂ).im) ≤ δ / 6 := by
        calc Real.exp (-π * (τ : ℂ).im) ≤ Real.exp (-Real.log (6 / δ)) := Real.exp_le_exp.mpr this
          _ = δ / 6 := by
            rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
      linarith
    have h2 := norm_sub_norm_le D (jacobiTheta₂ (shiftedPoint N 0 b τ) τ)
    rw [norm_sub_rev] at h2
    linarith

/-- Bound on a representative pair. -/
theorem F_bounded_rep (hN : 0 < N) {a b : ℤ}
    (hrep : (1 - (N : ℤ) ≤ a ∧ a ≤ -1) ∨ (a = 0 ∧ ¬ (N : ℤ) ∣ b)) :
    ∃ M A : ℝ, ∀ τ : ℍ, A ≤ τ.im → ‖F N (a, b) τ‖ ≤ M := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨c, hc, A, hA1, hlow⟩ := exists_theta_lower hN hrep
  refine ⟨‖(a : ℂ) / N + 1 / 2‖ + Kθ / c, A, fun τ hτ => ?_⟩
  have hy1 : 1 ≤ (τ : ℂ).im := le_trans hA1 hτ
  have hy : 0 < (τ : ℂ).im := τ.im_pos
  have hθ := hlow τ hτ
  have hz : |(shiftedPoint N a b τ).im| ≤ (τ : ℂ).im / 2 := by
    have him : (shiftedPoint N a b τ).im = ((a : ℝ) / N + 1 / 2) * (τ : ℂ).im := zc_im N a b τ
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
  have hθ' : ‖jacobiTheta₂' (shiftedPoint N a b τ) τ‖ ≤ Kθ := norm_theta'_le hy1 hz
  rw [F_apply]
  have hden : c ≤ ‖2 * (π : ℂ) * I * jacobiTheta₂ (shiftedPoint N a b τ) τ‖ := by
    rw [norm_mul, norm_two_pi_I]
    nlinarith [Real.pi_gt_three, norm_nonneg (jacobiTheta₂ (shiftedPoint N a b τ) τ)]
  have hK : 0 ≤ Kθ := le_trans (norm_nonneg _) hθ'
  have hq : ‖logDer (shiftedPoint N a b τ) τ‖ ≤ Kθ / c := by
    unfold logDer
    rw [norm_div]
    calc ‖jacobiTheta₂' (shiftedPoint N a b τ) τ‖ /
          ‖2 * (π : ℂ) * I * jacobiTheta₂ (shiftedPoint N a b τ) τ‖
        ≤ Kθ / ‖2 * (π : ℂ) * I * jacobiTheta₂ (shiftedPoint N a b τ) τ‖ :=
          div_le_div_of_nonneg_right hθ' (norm_nonneg _)
      _ ≤ Kθ / c := div_le_div_of_nonneg_left hK hc hden
  calc ‖(a : ℂ) / N + 1 / 2 + logDer (shiftedPoint N a b τ) τ‖
      ≤ ‖(a : ℂ) / N + 1 / 2‖ + ‖logDer (shiftedPoint N a b τ) τ‖ := norm_add_le _ _
    _ ≤ ‖(a : ℂ) / N + 1 / 2‖ + Kθ / c := by linarith

/-- Every admissible `F_v` is bounded at `i∞`. -/
theorem F_isBoundedAtImInfty (hN : 0 < N) {v : ℤ × ℤ} (h : Good N v) :
    UpperHalfPlane.IsBoundedAtImInfty (F N v) := by
  obtain ⟨a, b⟩ := v
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  have hqr := Int.mul_ediv_add_emod a N
  have hr0 := Int.emod_nonneg a hNz.ne'
  have hr1 := Int.emod_lt_of_pos a hNz
  by_cases ha : a % N = 0
  · have hb : ¬ (N : ℤ) ∣ b := fun hb => h ⟨Int.dvd_of_emod_eq_zero ha, hb⟩
    have hg : Good N (0, b) := fun h' => hb h'.2
    obtain ⟨M, A, hMA⟩ := F_bounded_rep hN (a := 0) (b := b) (Or.inr ⟨rfl, hb⟩)
    refine ⟨M, A, fun τ hτ => ?_⟩
    rw [show ((a, b) : ℤ × ℤ) = (0 + N * (a / N), b + N * 0) from
      Prod.ext (by dsimp only; rw [ha] at hqr; linarith) (by dsimp only; ring), F_shift hN hg]
    exact hMA τ hτ
  · have hrep : 1 - (N : ℤ) ≤ a % N - N ∧ a % N - N ≤ -1 := by
      constructor
      · have : 0 < a % N := lt_of_le_of_ne hr0 (Ne.symm ha)
        linarith
      · linarith
    have hg : Good N (a % N - N, b) := by
      rintro ⟨h1, _⟩
      obtain ⟨k, hk⟩ := h1
      have h1 : 1 - (N : ℤ) ≤ N * k := hk ▸ hrep.1
      have h2 : (N : ℤ) * k ≤ -1 := hk ▸ hrep.2
      have hk1 : k < 0 := by
        by_contra hk0
        push Not at hk0
        nlinarith
      have hk2 : -1 < k := by
        by_contra hk0
        push Not at hk0
        nlinarith
      omega
    obtain ⟨M, A, hMA⟩ := F_bounded_rep hN (a := a % N - N) (b := b) (Or.inl hrep)
    refine ⟨M, A, fun τ hτ => ?_⟩
    rw [show ((a, b) : ℤ × ℤ) = ((a % N - N) + N * (a / N + 1), b + N * 0) from
      Prod.ext (by dsimp only; linarith) (by dsimp only; ring), F_shift hN hg]
    exact hMA τ hτ

/-! ### Level `Γ₁(N)` and the modular forms -/

theorem F_slash_Gamma1 (hN : 0 < N) {b : ℤ} (hb : ¬ (N : ℤ) ∣ b) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) : F N (0, b) ∣[(1 : ℤ)] γ = F N (0, b) := by
  have hg : Good N (0, b) := fun h => hb h.2
  rw [F_slash hN γ _ hg]
  rw [CongruenceSubgroup.Gamma1_mem] at hγ
  obtain ⟨_, h11, h10⟩ := hγ
  have h10' : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp h10
  have h11'' : ((γ 1 1 : ℤ) : ZMod N) = ((1 : ℤ) : ZMod N) := by simpa using h11
  have h11' : (N : ℤ) ∣ 1 - γ 1 1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mp h11''
  obtain ⟨m, hm⟩ := h10'
  obtain ⟨n, hn⟩ := h11'
  have hact : act (0, b) γ = (0 + N * (b * m), b + N * (-(b * n))) := by
    refine Prod.ext ?_ ?_
    · dsimp only [act]; rw [hm]; ring
    · dsimp only [act]; linear_combination (-b) * hn
  rw [hact]
  funext τ
  exact F_shift hN hg _ _ τ

theorem F_bdd_cusp (hN : 0 < N) {b : ℤ} (hb : ¬ (N : ℤ) ∣ b) {c : OnePoint ℝ}
    (hc : IsCusp c ((CongruenceSubgroup.Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ))) :
    c.IsBoundedAt (F N (0, b)) 1 := by
  have hg : Good N (0, b) := fun h => hb h.2
  have hc' : IsCusp c 𝒮ℒ := IsCusp.mono (Subgroup.map_le_range _ _) hc
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
  intro γ _
  rw [F_slash hN γ _ hg]
  exact F_isBoundedAtImInfty hN (good_act hg γ)

/-- **The weight-one modular form** on `Γ₁(N)` with underlying function
`torsionLogDerivative N 0 b`, for a positive level `N` and `b` not divisible by `N`. -/
def torsionForm (N : ℕ) (hN : 0 < N) (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) :
    ModularForm ((CongruenceSubgroup.Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 1 where
  toFun := F N (0, b)
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    have := F_slash_Gamma1 hN hb g hg
    rwa [ModularForm.SL_slash] at this
  holo' := UpperHalfPlane.mdifferentiable_iff.mpr (F_diffOn hN (fun h => hb h.2))
  bdd_at_cusps' hc := F_bdd_cusp hN hb hc

theorem torsionForm_apply (N : ℕ) (hN : 0 < N) (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) (τ : ℍ) :
    torsionForm N hN b hb τ = torsionLogDerivative N 0 b τ := rfl

end ZInQ.Contrib.HeckePrimeRationality.AllLevelForms
