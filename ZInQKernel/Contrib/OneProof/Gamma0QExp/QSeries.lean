import ZInQKernel.Contrib.OneProof.Gamma0QExp.Descent
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_hasSum_jq_qParam
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# gamma0-qexp, part 2: `q`-series valid on all of `ℍ`

`Rz L F`: the Laurent series `L ∈ ℂ((q))` sums to `F(τ)` at every `τ ∈ ℍ` (`q = e^{2πiτ}`).
Closure under ring operations and polynomial evaluation (FLT's `hasSum_qParam_mul_laurent`),
`j` and `j(Nτ)`, shifts `τ ↦ τ + it` (FLT's `qTwist`), continuity of the sum (FLT's
`Realized.mdifferentiable`), and the vanishing criterion: if `Rz (qTwist r L) (F ∘ shift)` and
`F` vanishes on a punctured neighbourhood of every point of `ℍ`, then `L = 0`.

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane ModularCurve Filter Topology


namespace ZInQ.Gamma0QExp

/-- Klein's `j = E₄³/Δ`. -/
def jf (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

theorem natCast_mul_im_pos (N : ℕ) [NeZero N] (τ : ℍ) : 0 < ((N : ℂ) * τ).im := by
  rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) τ.im_pos

/-- `τ ↦ Nτ`. -/
def scaleN (N : ℕ) [NeZero N] (τ : ℍ) : ℍ := ⟨(N : ℂ) * τ, natCast_mul_im_pos N τ⟩

@[simp] theorem coe_scaleN (N : ℕ) [NeZero N] (τ : ℍ) : ((scaleN N τ : ℍ) : ℂ) = N * τ := rfl

/-- `j(Nτ)`. -/
def jN (N : ℕ) [NeZero N] (τ : ℍ) : ℂ := jf (scaleN N τ)

/-- **`L` sums to `F` on all of `ℍ`.** -/
def Rz (L : LaurentSeries ℂ) (F : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun m : ℤ => L.coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)

namespace Rz

variable {L L' : LaurentSeries ℂ} {F G : ℍ → ℂ}

theorem mul (hL : Rz L F) (hL' : Rz L' G) : Rz (L * L') (fun τ => F τ * G τ) :=
  fun τ => hasSum_qParam_mul_laurent 1 one_pos L L' F G hL hL' τ

theorem add (hL : Rz L F) (hL' : Rz L' G) : Rz (L + L') (fun τ => F τ + G τ) := fun τ => by
  have := (hL τ).add (hL' τ)
  simpa only [HahnSeries.coeff_add, add_mul] using this

theorem neg (hL : Rz L F) : Rz (-L) (fun τ => -F τ) := fun τ => by
  have := (hL τ).neg
  simpa only [HahnSeries.coeff_neg, neg_mul] using this

theorem sub (hL : Rz L F) (hL' : Rz L' G) : Rz (L - L') (fun τ => F τ - G τ) := by
  simpa only [sub_eq_add_neg] using hL.add hL'.neg

theorem single (k : ℤ) (c : ℂ) : Rz (HahnSeries.single k c) (fun τ => c * Function.Periodic.qParam 1 (τ : ℂ) ^ k) :=
  fun τ => by
    convert hasSum_single (f := fun m : ℤ => (HahnSeries.single k c).coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      k (fun m hm => by rw [HahnSeries.coeff_single_of_ne hm, zero_mul]) using 1
    rw [HahnSeries.coeff_single_same]

theorem C (c : ℂ) : Rz (HahnSeries.C c) (fun _ => c) := by
  have := single 0 c
  simpa only [HahnSeries.C_apply, zpow_zero, mul_one] using this

theorem congr_fun (hL : Rz L F) (h : ∀ τ, F τ = G τ) : Rz L G := fun τ => h τ ▸ hL τ

theorem aeval {σ : Type*} (v : σ → LaurentSeries ℂ) (F : σ → ℍ → ℂ) (h : ∀ i, Rz (v i) (F i))
    (p : MvPolynomial σ ℂ) :
    Rz (MvPolynomial.aeval v p) (fun τ => MvPolynomial.eval (fun i => F i τ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, MvPolynomial.eval_C, algebraMap_laurentSeries_eq_single]
    simpa only [zpow_zero, mul_one] using single 0 a
  | add p q hp hq =>
    simp only [map_add, MvPolynomial.eval_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    exact hp.mul (h i)

/-- The zero criterion (FLT's `laurent_qParam_coeff_unique`). -/
theorem eq_zero (hL : Rz L F) (h : ∀ τ, F τ = 0) : L = 0 :=
  laurent_qParam_coeff_unique 1 one_pos F L 0 hL (fun τ => by
    simp only [HahnSeries.coeff_zero, zero_mul, h τ]; exact hasSum_zero)

end Rz

theorem coeffEmb_coeff_eq (x : LaurentSeries ℚ) (m : ℤ) :
    (coeffEmb ℂ x).coeff m = ((x.coeff m : ℚ) : ℂ) := by
  rw [coeffEmb_coeff]; rfl

theorem rz_jq : Rz (coeffEmb ℂ jq) jf := fun τ => by
  simpa only [coeffEmb_coeff_eq, jf] using hasSum_jq_qParam τ

theorem qParam_scaleN (N : ℕ) [NeZero N] (τ : ℍ) :
    Function.Periodic.qParam 1 ((scaleN N τ : ℍ) : ℂ) = Function.Periodic.qParam 1 (τ : ℂ) ^ N := by
  simp only [Function.Periodic.qParam, coe_scaleN, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  ring_nf

theorem rz_jqN (N : ℕ) [NeZero N] : Rz (coeffEmb ℂ (jqN N)) (jN N) := fun τ => by
  have h := hasSum_jq_qParam (scaleN N τ)
  rw [qParam_scaleN] at h
  set q := Function.Periodic.qParam 1 (τ : ℂ)
  have hinj : Function.Injective (fun m : ℤ => (N : ℤ) * m) :=
    mul_right_injective₀ (by exact_mod_cast NeZero.ne N)
  rw [← hinj.hasSum_iff]
  · show HasSum _ (ModularForm.E₄ (scaleN N τ) ^ 3 / ModularForm.discriminant (scaleN N τ))
    convert h using 1
    funext m
    simp only [Function.comp_apply, coeffEmb_coeff_eq, jqN, qExpand_coeff_mul]
    rw [zpow_mul, zpow_natCast]
  · intro k hk
    have hk' : ¬ (N : ℤ) ∣ k := by
      rintro ⟨m, rfl⟩; exact hk ⟨m, rfl⟩
    rw [coeffEmb_coeff_eq, jqN, qExpand_coeff_of_not_dvd N jq hk']
    simp

/-- The shift `τ ↦ τ + it`, `t ≥ 0`. -/
def shiftH (t : ℝ) (ht : 0 ≤ t) (τ : ℍ) : ℍ :=
  ⟨τ + t * Complex.I, by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    have := τ.im_pos
    rw [UpperHalfPlane.coe_im]; linarith⟩

@[simp] theorem coe_shiftH (t : ℝ) (ht : 0 ≤ t) (τ : ℍ) :
    ((shiftH t ht τ : ℍ) : ℂ) = τ + t * Complex.I := rfl

theorem im_shiftH (t : ℝ) (ht : 0 ≤ t) (τ : ℍ) : (shiftH t ht τ).im = τ.im + t := by
  change (((τ : ℂ) + t * Complex.I)).im = τ.im + t
  simp

/-- The unit `e^{-2πt}`. -/
def rUnit (t : ℝ) : ℂˣ := Units.mk0 (Real.exp (-2 * Real.pi * t) : ℂ)
  (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')

theorem qParam_shiftH (t : ℝ) (ht : 0 ≤ t) (τ : ℍ) :
    Function.Periodic.qParam 1 ((shiftH t ht τ : ℍ) : ℂ) = (rUnit t : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) := by
  simp only [Function.Periodic.qParam, coe_shiftH, Complex.ofReal_one, div_one, rUnit,
    Units.val_mk0, Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem rz_qTwist_of {L : LaurentSeries ℂ} {F : ℍ → ℂ} (t : ℝ) (ht : 0 ≤ t)
    (h : ∀ τ : ℍ, HasSum (fun m : ℤ => L.coeff m * Function.Periodic.qParam 1 ((shiftH t ht τ : ℍ) : ℂ) ^ m)
      (F (shiftH t ht τ))) :
    Rz (qTwist (rUnit t) L) (F ∘ shiftH t ht) := fun τ => by
  have := h τ
  rw [qParam_shiftH] at this
  show HasSum _ (F (shiftH t ht τ))
  convert this using 1
  funext m
  rw [qTwist_coeff, Units.val_zpow_eq_zpow_val, mul_zpow]
  ring

theorem rz_qTwist {L : LaurentSeries ℂ} {F : ℍ → ℂ} (t : ℝ) (ht : 0 ≤ t) (hL : Rz L F) :
    Rz (qTwist (rUnit t) L) (F ∘ shiftH t ht) :=
  rz_qTwist_of t ht fun τ => hL _

theorem qTwist_aeval {σ : Type*} (u : ℂˣ) (v : σ → LaurentSeries ℂ) (p : MvPolynomial σ ℂ) :
    qTwist u (MvPolynomial.aeval v p) = MvPolynomial.aeval (fun i => qTwist u (v i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, algebraMap_laurentSeries_eq_single]
    ext m
    rw [qTwist_coeff]
    by_cases hm : m = 0
    · subst hm; simp
    · rw [HahnSeries.coeff_single_of_ne hm, mul_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X]

theorem qTwist_injective (u : ℂˣ) : Function.Injective (qTwist u) := by
  intro a b h
  ext m
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff m) h
  simp only [qTwist_coeff] at this
  exact (Units.mul_right_inj _).1 this

/-! ### Continuity of the sum of a `q`-series -/

theorem exists_coeff_eq_zero_below (L : LaurentSeries ℂ) :
    ∃ k : ℕ, ∀ m : ℤ, m < -(k : ℤ) → L.coeff m = 0 := by
  by_cases hL : L = 0
  · exact ⟨0, fun m _ => by rw [hL]; rfl⟩
  · refine ⟨(-L.order).toNat, fun m hm => HahnSeries.coeff_eq_zero_of_lt_order ?_⟩
    have := Int.self_le_toNat (-L.order)
    omega

theorem continuousAt_of_rz {L : LaurentSeries ℂ} {F : ℍ → ℂ} (hL : Rz L F) (τ : ℍ) :
    ContinuousAt (F ∘ ofComplex) (τ : ℂ) := by
  obtain ⟨k, hk⟩ := exists_coeff_eq_zero_below L
  set L' := HahnSeries.single (k : ℤ) (1 : ℂ) * L
  have hL' : Rz L' (fun τ => Function.Periodic.qParam 1 (τ : ℂ) ^ k * F τ) := by
    have := (Rz.single (k : ℤ) (1 : ℂ)).mul hL
    simpa only [one_mul, zpow_natCast] using this
  have hc : ∀ σ : ℍ, HasSum (fun n : ℕ => L'.coeff n * Function.Periodic.qParam 1 (σ : ℂ) ^ n)
      (Function.Periodic.qParam 1 (σ : ℂ) ^ k * F σ) := by
    intro σ
    have h := hL' σ
    rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff] at h
    · convert h using 1
      funext n
      simp only [Function.comp_apply, zpow_natCast]
    · intro m hm
      have hm0 : m < 0 := by
        by_contra h0; push Not at h0; exact hm ⟨m.toNat, Int.toNat_of_nonneg h0⟩
      simp only [L', HahnSeries.coeff_single_mul, one_mul]
      rw [hk _ (by omega), zero_mul]
  have hmd := P2MW.S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.ModularCurve.Realized.mdifferentiable
    one_pos hc
  have hd := (mdifferentiableAt_iff.mp (hmd τ)).continuousAt
  have hq : ContinuousAt (fun z : ℂ => Function.Periodic.qParam 1 z ^ k) (τ : ℂ) :=
    ((Function.Periodic.differentiable_qParam (h := 1)).continuous.pow k).continuousAt
  have hq0 : Function.Periodic.qParam 1 (τ : ℂ) ^ k ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hdiv := hd.div hq hq0
  refine hdiv.congr ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  simp only [Pi.div_apply, Function.comp_apply, ofComplex_apply_of_im_pos hz]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (Complex.exp_ne_zero _))

/-! ### The vanishing criterion -/

theorem tendsto_add_nhdsNE (a c : ℂ) :
    Tendsto (fun z : ℂ => z + c) (𝓝[≠] a) (𝓝[≠] (a + c)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact ((continuous_id.add continuous_const).tendsto a).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz

/-- **The vanishing criterion.** -/
theorem eq_zero_of_rz_shift {L : LaurentSeries ℂ} {F : ℍ → ℂ} (t : ℝ) (ht : 0 ≤ t)
    (hL : Rz (qTwist (rUnit t) L) (F ∘ shiftH t ht))
    (hF : ∀ w : ℍ, ∀ᶠ z in 𝓝[≠] (w : ℂ), F (ofComplex z) = 0) : L = 0 := by
  apply qTwist_injective (rUnit t)
  rw [map_zero]
  refine hL.eq_zero fun τ => ?_
  have hc := continuousAt_of_rz hL τ
  -- `F ∘ shift` vanishes on a punctured neighbourhood of `τ`
  have hev : ∀ᶠ z in 𝓝[≠] (τ : ℂ), ((F ∘ shiftH t ht) ∘ ofComplex) z = 0 := by
    have h1 := (tendsto_add_nhdsNE (τ : ℂ) (t * Complex.I)).eventually (hF (shiftH t ht τ))
    have h2 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
      nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
    filter_upwards [h1, h2] with z hz hzim
    have hzim' : 0 < (z + t * Complex.I).im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
      linarith
    simp only [Function.comp_apply]
    convert hz using 2
    apply UpperHalfPlane.ext
    rw [coe_shiftH, ofComplex_apply_of_im_pos hzim, ofComplex_apply_of_im_pos hzim']
  have hlim : Tendsto ((F ∘ shiftH t ht) ∘ ofComplex) (𝓝[≠] (τ : ℂ))
      (𝓝 (((F ∘ shiftH t ht) ∘ ofComplex) (τ : ℂ))) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have h0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm))
  simpa only [Function.comp_apply, ofComplex_apply] using h0

end ZInQ.Gamma0QExp
