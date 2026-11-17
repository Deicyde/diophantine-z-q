import ZInQKernel.Contrib.GZTheta.Eta32

/-!
# gz-theta: `η(4τ)² η(8τ)²` as a cusp form of weight 2 on `Γ₀(32)`

* Cusps. For `γ ∈ SL(2, ℤ)` and `m > 0`, `diag(m, 1) γ = γ₁ (α β; 0 δ)` with `γ₁ ∈ SL(2, ℤ)`,
  `α, δ > 0` (Hermite), so `η(m γτ)² = ζ^e (cτ + d)/δ · η((ατ + β)/δ)²` by `eta_sq_mobius`.
  Hence `(η(4·)² η(8·)²) ∣[2] γ` is a constant times a product of two functions `η(wᵢ)²` with
  `Im wᵢ → ∞`, and `η → 0` at `i∞` (from Mathlib's `discriminant_isZeroAtImInfty`).
* `etaForm32 : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2`.
-/

open Complex ModularForm Matrix.SpecialLinearGroup CongruenceSubgroup Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups Topology

noncomputable section

namespace ZInQ.GZTheta

/-! ### Hermite decomposition -/

/-- `diag(m, 1) (a b; c d) = (a' b'; c' d') (α β; 0 δ)` with `a' d' − b' c' = 1`, `α, δ > 0`. -/
theorem exists_hermite {m : ℤ} (hm : 0 < m) {a b c d : ℤ} (hdet : a * d - b * c = 1) :
    ∃ a' b' c' d' α β δ : ℤ, a' * d' - b' * c' = 1 ∧ 0 < α ∧ 0 < δ ∧
      m * a = a' * α ∧ m * b = a' * β + b' * δ ∧ c = c' * α ∧ d = c' * β + d' * δ := by
  set g : ℤ := ((m * a).gcd c : ℤ) with hg
  have hg0 : 0 < g := by
    rw [hg]
    have : (m * a).gcd c ≠ 0 := by
      intro h0
      rw [Int.gcd_eq_zero_iff] at h0
      have ha : a = 0 := by
        rcases mul_eq_zero.mp h0.1 with h | h
        · omega
        · exact h
      rw [ha, h0.2] at hdet
      simp at hdet
    exact_mod_cast Nat.pos_of_ne_zero this
  obtain ⟨a', ha'⟩ : g ∣ m * a := Int.gcd_dvd_left _ _
  obtain ⟨c', hc'⟩ : g ∣ c := Int.gcd_dvd_right _ _
  -- `gcd(a', c') = 1`, Bezout
  have hcop : Int.gcd a' c' = 1 := by
    have h1 : Int.gcd (m * a) c = Int.gcd (g * a') (g * c') := by rw [← ha', ← hc']
    rw [Int.gcd_mul_left] at h1
    have hG : g.natAbs = (m * a).gcd c := by rw [hg, Int.natAbs_natCast]
    rw [hG] at h1
    have hGpos : 0 < (m * a).gcd c := by
      have : (0 : ℤ) < ((m * a).gcd c : ℤ) := hg ▸ hg0
      exact_mod_cast this
    exact Nat.eq_of_mul_eq_mul_left hGpos (h1.symm.trans (mul_one _).symm)
  have hbez := Int.gcd_eq_gcd_ab a' c'
  rw [hcop] at hbez
  set u := Int.gcdA a' c'
  set v := Int.gcdB a' c'
  refine ⟨a', -v, c', u, g, u * (m * b) + v * d, -c' * (m * b) + a' * d, ?_, hg0, ?_, ?_, ?_, ?_, ?_⟩
  · push_cast at hbez; linear_combination -hbez
  · -- `α δ = m`
    have hαδ : g * (-c' * (m * b) + a' * d) = m := by
      have e1 : g * (-c' * (m * b) + a' * d) = -(g * c') * (m * b) + (g * a') * d := by ring
      rw [e1, ← hc', ← ha']
      linear_combination m * hdet
    by_contra hneg
    rw [not_lt] at hneg
    have : g * (-c' * (m * b) + a' * d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hg0.le hneg
    linarith
  · rw [ha']; ring
  · push_cast at hbez
    linear_combination (m * b) * hbez
  · rw [hc']; ring
  · push_cast at hbez
    linear_combination d * hbez


/-! ### `η(m γτ)²` -/

theorem im_affine (α β δ : ℤ) (τ : ℂ) :
    (((α : ℂ) * τ + β) / δ).im = α * τ.im / δ := by
  rw [Complex.div_intCast_im]
  simp

theorem im_affine_pos {α δ : ℤ} (hα : 0 < α) (hδ : 0 < δ) (β : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    0 < (((α : ℂ) * τ + β) / δ).im := by
  rw [im_affine]
  have h1 : (0 : ℝ) < α := by exact_mod_cast hα
  have h2 : (0 : ℝ) < δ := by exact_mod_cast hδ
  positivity

theorem eta_sq_mul_smul {m : ℤ} (hm : 0 < m) (γ : SL(2, ℤ)) :
    ∃ (C : ℂ) (α β δ : ℤ), 0 < α ∧ 0 < δ ∧ ∀ τ : ℍ,
      η (m * ((γ • τ : ℍ) : ℂ)) ^ 2 =
        C * ((γ 1 0 : ℂ) * τ + γ 1 1) * η (((α : ℂ) * τ + β) / δ) ^ 2 := by
  obtain ⟨a', b', c', d', α, β, δ, hdet', hα, hδ, e1, e2, e3, e4⟩ :=
    exists_hermite hm (det_SL γ)
  refine ⟨zeta12 ^ etaSqExp c'.natAbs a' b' c' d' / δ, α, β, δ, hα, hδ, fun τ => ?_⟩
  have hτ := τ.im_pos
  have hδ0 : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hw : 0 < (((α : ℂ) * τ + β) / δ).im := im_affine_pos hα hδ β hτ
  have hD : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := mobius_denom_ne_zero (det_SL γ) hτ
  set w : ℂ := ((α : ℂ) * τ + β) / δ with hwdef
  have hD' : (c' : ℂ) * w + d' ≠ 0 := mobius_denom_ne_zero hdet' hw
  have hcw : (c' : ℂ) * w + d' = ((γ 1 0 : ℂ) * τ + γ 1 1) / δ := by
    rw [hwdef]
    have h3 : ((γ 1 0 : ℤ) : ℂ) = (c' : ℂ) * α := by rw [e3]; push_cast; ring
    have h4 : ((γ 1 1 : ℤ) : ℂ) = (c' : ℂ) * β + d' * δ := by rw [e4]; push_cast; ring
    rw [h3, h4]
    field_simp
    ring
  have hmw : (m : ℂ) * ((γ • τ : ℍ) : ℂ) = ((a' : ℂ) * w + b') / ((c' : ℂ) * w + d') := by
    rw [coe_smul_SL, hcw]
    have h1 : (m : ℂ) * (γ 0 0 : ℂ) = (a' : ℂ) * α := by exact_mod_cast e1
    have h2 : (m : ℂ) * (γ 0 1 : ℂ) = (a' : ℂ) * β + b' * δ := by exact_mod_cast e2
    have hnum : (δ : ℂ) * ((a' : ℂ) * w + b') = m * ((γ 0 0 : ℂ) * τ + γ 0 1) := by
      rw [hwdef, mul_add, ← mul_assoc, mul_comm (δ : ℂ) (a' : ℂ), mul_assoc,
        mul_div_cancel₀ _ hδ0]
      linear_combination (-(τ : ℂ)) * h1 - h2
    rw [div_div_eq_mul_div, mul_comm _ (δ : ℂ), hnum, mul_div_assoc]
  rw [hmw, eta_sq_mobius c'.natAbs a' b' c' d' le_rfl hdet' w hw, hcw]
  field_simp

/-! ### `η → 0` at `i∞` -/

theorem tendsto_eta_sq_atImInfty :
    Tendsto (fun τ : ℍ => η (τ : ℂ) ^ 2) atImInfty (𝓝 0) := by
  have hΔ : Tendsto discriminant atImInfty (𝓝 0) := discriminant_isZeroAtImInfty
  rw [Metric.tendsto_nhds] at hΔ ⊢
  intro ε hε
  filter_upwards [hΔ (ε ^ 12) (pow_pos hε 12)] with τ hτ
  rw [dist_zero_right] at hτ ⊢
  have e : ‖η (τ : ℂ) ^ 2‖ ^ 12 = ‖discriminant τ‖ := by
    rw [discriminant, ← norm_pow, ← pow_mul]
  rw [← e] at hτ
  exact lt_of_pow_lt_pow_left₀ 12 hε.le hτ

theorem tendsto_affine_atImInfty {α δ : ℤ} (hα : 0 < α) (hδ : 0 < δ) (β : ℤ)
    (w : ℍ → ℍ) (hw : ∀ τ : ℍ, ((w τ : ℍ) : ℂ) = ((α : ℂ) * τ + β) / δ) :
    Tendsto w atImInfty atImInfty := by
  unfold atImInfty
  rw [tendsto_comap_iff]
  have him : ∀ τ : ℍ, (w τ).im = (α / δ : ℝ) * τ.im := by
    intro τ
    have := congrArg Complex.im (hw τ)
    rw [UpperHalfPlane.coe_im, im_affine] at this
    rw [this, UpperHalfPlane.coe_im]
    ring
  have hpos : (0 : ℝ) < α / δ := div_pos (by exact_mod_cast hα) (by exact_mod_cast hδ)
  have : Tendsto (fun τ : ℍ => (α / δ : ℝ) * τ.im) atImInfty atTop :=
    (tendsto_comap.const_mul_atTop hpos)
  exact this.congr (fun τ => (him τ).symm)

/-- `η((ατ + β)/δ)² → 0` as `Im τ → ∞`. -/
theorem tendsto_eta_sq_affine {α δ : ℤ} (hα : 0 < α) (hδ : 0 < δ) (β : ℤ) :
    Tendsto (fun τ : ℍ => η (((α : ℂ) * τ + β) / δ) ^ 2) atImInfty (𝓝 0) := by
  have hw : Tendsto (fun τ : ℍ => UpperHalfPlane.mk (((α : ℂ) * τ + β) / δ)
      (im_affine_pos hα hδ β τ.im_pos)) atImInfty atImInfty :=
    tendsto_affine_atImInfty hα hδ β _ (fun τ => UpperHalfPlane.coe_mk _ _)
  refine (tendsto_eta_sq_atImInfty.comp hw).congr (fun τ => ?_)
  rw [Function.comp_apply, UpperHalfPlane.coe_mk]

/-- **Vanishing at every cusp.** -/
theorem etaQuot32_slash_isZeroAtImInfty (γ : SL(2, ℤ)) :
    IsZeroAtImInfty (etaQuot32 ∣[(2 : ℤ)] γ) := by
  obtain ⟨C₁, α₁, β₁, δ₁, hα₁, hδ₁, h₁⟩ := eta_sq_mul_smul (m := 4) (by norm_num) γ
  obtain ⟨C₂, α₂, β₂, δ₂, hα₂, hδ₂, h₂⟩ := eta_sq_mul_smul (m := 8) (by norm_num) γ
  have key : (etaQuot32 ∣[(2 : ℤ)] γ) = fun τ : ℍ =>
      C₁ * C₂ * (η (((α₁ : ℂ) * τ + β₁) / δ₁) ^ 2 * η (((α₂ : ℂ) * τ + β₂) / δ₂) ^ 2) := by
    ext τ
    rw [SL_slash_apply]
    have hD : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := mobius_denom_ne_zero (det_SL γ) τ.im_pos
    have hden : denom γ τ = (γ 1 0 : ℂ) * τ + γ 1 1 := by simp [ModularGroup.denom_apply]
    unfold etaQuot32
    have h₁' := h₁ τ
    have h₂' := h₂ τ
    push_cast at h₁' h₂'
    rw [h₁', h₂', hden, zpow_neg, zpow_two]
    field_simp
  rw [key, IsZeroAtImInfty, ZeroAtFilter]
  have := ((tendsto_eta_sq_affine hα₁ hδ₁ β₁).mul (tendsto_eta_sq_affine hα₂ hδ₂ β₂)).const_mul
    (C₁ * C₂)
  simpa using this


/-! ### The cusp form -/

theorem differentiableAt_etaQuot32 {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (fun z : ℂ => η (4 * z) ^ 2 * η (8 * z) ^ 2) z := by
  have h4 : (4 * z) ∈ upperHalfPlaneSet := by
    show 0 < (4 * z).im; simp; exact hz
  have h8 : (8 * z) ∈ upperHalfPlaneSet := by
    show 0 < (8 * z).im; simp; exact hz
  have d4 : DifferentiableAt ℂ (fun z : ℂ => η (4 * z)) z :=
    (differentiableAt_eta_of_mem_upperHalfPlaneSet h4).comp z
      ((differentiableAt_id).const_mul 4)
  have d8 : DifferentiableAt ℂ (fun z : ℂ => η (8 * z)) z :=
    (differentiableAt_eta_of_mem_upperHalfPlaneSet h8).comp z
      ((differentiableAt_id).const_mul 8)
  exact (d4.pow 2).mul (d8.pow 2)

/-- **`η(4τ)² η(8τ)² ∈ S₂(Γ₀(32))`.** -/
def etaForm32 : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2 where
  toFun := etaQuot32
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    have h := etaQuot32_slash_eq hγ
    rw [ModularForm.SL_slash] at h
    exact h
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine .congr (fun z hz => (differentiableAt_etaQuot32 hz).differentiableWithinAt)
      fun z hz => ?_
    simp [etaQuot32, ofComplex_apply_of_im_pos hz]
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    exact etaQuot32_slash_isZeroAtImInfty γ

theorem coe_etaForm32 : (etaForm32 : ℍ → ℂ) = etaQuot32 := rfl

end ZInQ.GZTheta
