import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelWeierstrassDistributionNat
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# Transformation law of the theta finite-part constant

Let `c(τ) = ThetaWeierstrass.finitePart τ` be the constant with
`℘_τ(z) = -(H'/H)'(z) + c(τ)` for the completed theta function `H`. This file proves
`c(τ + 1) = c(τ)` and `c(-1/τ) = τ² c(τ) + 2π i τ`, directly from the theta transformation
laws (Mathlib's functional equation of `jacobiTheta₂`) and the Laurent characterisation of `c`.

Consequently `F = c + G2`, with Mathlib's Eisenstein series `G2`, is invariant under the weight-two
slash action of every `γ ∈ SL(2, ℤ)` (`F_slash`). This is the transformation law expected of
`c = -G2`; holomorphy in `τ` and the behaviour at the cusp are not proved here, so the identity
`c = -G2` itself is not asserted.
-/

noncomputable section

open Complex Filter Topology ModularGroup
open scoped Real UpperHalfPlane MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.ThetaG2

open CompletedTheta ThetaWeierstrass WeierstrassDistributionNat

/-! ### The `T` law -/

theorem H_T (τ : ℍ) : H (T • τ) = H τ := by
  funext x
  unfold H
  rw [ThetaFive.coe_T_smul, ThetaFive.jacobiTheta₂_add_one_right]
  have e : x + ((τ : ℂ) + 1 + 1) / 2 + 1 / 2 = (x + ((τ : ℂ) + 1) / 2) + ((1 : ℤ) : ℂ) := by
    push_cast; ring
  rw [e, ThetaFive.jacobiTheta₂_add_int_left]

theorem finitePart_T (τ : ℍ) : finitePart (T • τ) = finitePart τ := by
  simp only [finitePart, H_T]

/-! ### The `S` law for `H` -/

/-- The quadratic exponent of the `S` transformation. -/
def Q (τ : ℍ) (x : ℂ) : ℂ :=
  π * I * x + π * I * ((τ : ℂ) * x + ((τ : ℂ) - 1) / 2) ^ 2 / τ - π * I * τ * x

/-- The multiplier of the `S` transformation. -/
def g (τ : ℍ) (x : ℂ) : ℂ := (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * cexp (Q τ x)

theorem H_S (τ : ℍ) (x : ℂ) : H (S • τ) x = g τ x * H τ ((τ : ℂ) * x) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hA : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ h.1
  set W : ℂ := (τ : ℂ) * x + ((τ : ℂ) - 1) / 2 with hW
  have hfe := jacobiTheta₂_functional_equation W (τ : ℂ)
  have hW1 : W / τ = x + (-1 / (τ : ℂ) + 1) / 2 := by rw [hW]; field_simp; ring
  have hθW : jacobiTheta₂ W τ = jacobiTheta₂ ((τ : ℂ) * x + ((τ : ℂ) + 1) / 2) τ := by
    rw [show W = ((τ : ℂ) * x + ((τ : ℂ) + 1) / 2) + ((-1 : ℤ) : ℂ) by rw [hW]; push_cast; ring,
      ThetaFive.jacobiTheta₂_add_int_left]
  rw [hW1, hθW] at hfe
  unfold H g
  rw [ThetaFive.coe_S_smul]
  have hQ : cexp (Q τ x) = cexp (π * I * x) * cexp (π * I * W ^ 2 / τ) *
      cexp (-(π * I * τ * x)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, Q, hW]
    ring_nf
  have hinv : cexp (π * I * W ^ 2 / τ) * cexp (-π * I * W ^ 2 / τ) = 1 := by
    rw [← Complex.exp_add]; convert Complex.exp_zero using 2; ring
  have hinv2 : cexp (-(π * I * τ * x)) * cexp (π * I * ((τ : ℂ) * x)) = 1 := by
    rw [← Complex.exp_add]; convert Complex.exp_zero using 2; ring
  rw [hQ]
  generalize jacobiTheta₂ (x + (-1 / (τ : ℂ) + 1) / 2) (-1 / τ) = θS at hfe ⊢
  generalize jacobiTheta₂ ((τ : ℂ) * x + ((τ : ℂ) + 1) / 2) τ = θ at hfe ⊢
  generalize cexp (π * I * W ^ 2 / τ) = E1 at hinv ⊢
  generalize cexp (-π * I * W ^ 2 / τ) = E2 at hinv hfe ⊢
  generalize cexp (-(π * I * τ * x)) = E3 at hinv2 ⊢
  generalize cexp (π * I * ((τ : ℂ) * x)) = E4 at hinv2 ⊢
  generalize cexp (π * I * x) = e1
  generalize (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) = A at hA hfe ⊢
  have hAinv : A * (1 / A) = 1 := by field_simp
  have h1 : θS = A * E1 * θ := by
    rw [hfe]
    linear_combination (-θS) * hinv + (-(E1 * E2 * θS)) * hAinv
  linear_combination e1 * h1 + (-(A * e1 * E1 * θ)) * hinv2

/-! ### The logarithmic derivative under `S` -/

theorem hasDerivAt_g (τ : ℍ) (x : ℂ) :
    HasDerivAt (g τ) (g τ x * (2 * π * I * τ * x)) x := by
  have hQ : HasDerivAt (Q τ) (2 * π * I * τ * x) x := by
    have h1 : HasDerivAt (fun y : ℂ => π * I * y) (π * I) x := by
      simpa using (hasDerivAt_id x).const_mul (π * I : ℂ)
    have h2 : HasDerivAt (fun y : ℂ => π * I * ((τ : ℂ) * y + ((τ : ℂ) - 1) / 2) ^ 2 / τ)
        (π * I * (2 * ((τ : ℂ) * x + ((τ : ℂ) - 1) / 2) * τ) / τ) x := by
      have hl : HasDerivAt (fun y : ℂ => (τ : ℂ) * y + ((τ : ℂ) - 1) / 2) (τ : ℂ) x := by
        simpa using ((hasDerivAt_id x).const_mul (τ : ℂ)).add_const (((τ : ℂ) - 1) / 2)
      have hs := (hl.pow 2).const_mul (π * I : ℂ)
      have := hs.div_const (τ : ℂ)
      convert this using 1
      push_cast; ring
    have h3 : HasDerivAt (fun y : ℂ => π * I * τ * y) (π * I * τ) x := by
      simpa using (hasDerivAt_id x).const_mul (π * I * τ : ℂ)
    have h := (h1.add h2).sub h3
    convert h using 1
    · funext y; simp only [Q, Pi.add_apply, Pi.sub_apply]
    · have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
      field_simp
      ring
  have h := (hQ.cexp).const_mul ((-I * (τ : ℂ)) ^ (1 / 2 : ℂ))
  convert h using 1
  · funext y; simp only [g]
  · simp only [g]; ring

theorem g_ne_zero (τ : ℍ) (x : ℂ) : g τ x ≠ 0 := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ h.1

theorem hasDerivAt_H_S (τ : ℍ) (x : ℂ) :
    HasDerivAt (H (S • τ)) (g τ x * (2 * π * I * τ * x) * H τ ((τ : ℂ) * x) +
      g τ x * (Hder τ ((τ : ℂ) * x) * τ)) x := by
  have hfun : H (S • τ) = fun y => g τ y * H τ ((τ : ℂ) * y) := funext (H_S τ)
  rw [hfun]
  have hc : HasDerivAt (fun y : ℂ => H τ ((τ : ℂ) * y)) (Hder τ ((τ : ℂ) * x) * τ) x :=
    (hasDerivAt_H τ ((τ : ℂ) * x)).comp x (by simpa using (hasDerivAt_id x).const_mul (τ : ℂ))
  exact (hasDerivAt_g τ x).mul hc

/-- `G_{Sτ}(x) = 2π i τ x + τ G_τ(τ x)` where `H_τ(τ x) ≠ 0`. -/
theorem G_S (τ : ℍ) {x : ℂ} (hx : H τ ((τ : ℂ) * x) ≠ 0) :
    G (S • τ) x = 2 * π * I * τ * x + (τ : ℂ) * G τ ((τ : ℂ) * x) := by
  unfold G
  rw [(hasDerivAt_H_S τ x).deriv, H_S, deriv_H]
  have := g_ne_zero τ x
  field_simp

theorem deriv_G_S (τ : ℍ) {z : ℂ} (hz : H τ ((τ : ℂ) * z) ≠ 0) :
    deriv (G (S • τ)) z = 2 * π * I * τ + (τ : ℂ) ^ 2 * deriv (G τ) ((τ : ℂ) * z) := by
  have hopen : ∀ᶠ x in 𝓝 z, H τ ((τ : ℂ) * x) ≠ 0 :=
    ((differentiable_H τ).continuous.comp (continuous_const.mul continuous_id)).continuousAt
      |>.eventually_ne hz
  have heq : G (S • τ) =ᶠ[𝓝 z] fun x => 2 * π * I * τ * x + (τ : ℂ) * G τ ((τ : ℂ) * x) :=
    hopen.mono fun x hx => G_S τ hx
  rw [heq.deriv_eq]
  have hd : HasDerivAt (fun x => 2 * π * I * τ * x + (τ : ℂ) * G τ ((τ : ℂ) * x))
      (2 * π * I * τ + (τ : ℂ) * (deriv (G τ) ((τ : ℂ) * z) * τ)) z := by
    have h1 : HasDerivAt (fun x : ℂ => 2 * π * I * τ * x) (2 * π * I * τ) z := by
      simpa using (hasDerivAt_id z).const_mul (2 * π * I * τ : ℂ)
    have h2 : HasDerivAt (fun x : ℂ => G τ ((τ : ℂ) * x)) (deriv (G τ) ((τ : ℂ) * z) * τ) z :=
      ((differentiableAt_G τ hz).hasDerivAt).comp z
        (by simpa using (hasDerivAt_id z).const_mul (τ : ℂ))
    exact h1.add (h2.const_mul (τ : ℂ))
  rw [hd.deriv]
  ring

/-! ### The finite-part constant under `S` -/

theorem finitePart_S (τ : ℍ) :
    finitePart (S • τ) = (τ : ℂ) ^ 2 * finitePart τ + 2 * π * I * τ := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  set L := periodPair τ
  have hU : ((L.lattice : Set ℂ) \ {(0 : ℂ)})ᶜ ∈ 𝓝 (0 : ℂ) :=
    L.compl_lattice_sdiff_singleton_mem_nhds 0
  have hmul : Tendsto (fun z : ℂ => (τ : ℂ) * z) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun z : ℂ => (τ : ℂ) * z) (𝓝 0) (𝓝 0) :=
        (continuous_const.mul continuous_id : Continuous fun z : ℂ => (τ : ℂ) * z).tendsto' 0 0
          (mul_zero _)
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact mul_ne_zero hτ hz
  have hnear : ∀ᶠ z in 𝓝[≠] (0 : ℂ), H τ ((τ : ℂ) * z) ≠ 0 ∧ z ≠ 0 := by
    have hz0 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 0 := self_mem_nhdsWithin
    have hzU : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (τ : ℂ) * z ∈ ((L.lattice : Set ℂ) \ {(0 : ℂ)})ᶜ :=
      hmul.mono_right nhdsWithin_le_nhds |>.eventually_mem hU
    filter_upwards [hz0, hzU] with z hz0 hzU
    refine ⟨?_, hz0⟩
    rw [← notMem_iff_H_ne_zero]
    exact fun hm => hzU ⟨hm, mul_ne_zero hτ hz0⟩
  have hS := H_neg_logDerivative_finitePart (S • τ)
  have hT := (H_neg_logDerivative_finitePart τ).comp hmul
  have hR : Tendsto (fun z : ℂ => -(2 * π * I * τ) + (τ : ℂ) ^ 2 *
      (-(deriv (fun w : ℂ => deriv (H τ) w / H τ w) ((τ : ℂ) * z)) - 1 / ((τ : ℂ) * z) ^ 2))
      (𝓝[≠] (0 : ℂ)) (𝓝 (-(2 * π * I * τ) + (τ : ℂ) ^ 2 * (-finitePart τ))) :=
    (hT.const_mul _).const_add _
  have hident : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      -(deriv (fun w : ℂ => deriv (H (S • τ)) w / H (S • τ) w) z) - 1 / z ^ 2 =
        -(2 * π * I * τ) + (τ : ℂ) ^ 2 *
          (-(deriv (fun w : ℂ => deriv (H τ) w / H τ w) ((τ : ℂ) * z)) - 1 / ((τ : ℂ) * z) ^ 2) := by
    filter_upwards [hnear] with z ⟨hz, hz0⟩
    have h := deriv_G_S τ hz
    change deriv (G (S • τ)) z = _ at h
    change -(deriv (G (S • τ)) z) - 1 / z ^ 2 = -(2 * π * I * τ) + (τ : ℂ) ^ 2 *
      (-(deriv (G τ) ((τ : ℂ) * z)) - 1 / ((τ : ℂ) * z) ^ 2)
    rw [h]
    field_simp
    ring
  have hlim := tendsto_nhds_unique hS (hR.congr' (hident.mono fun z hz => hz.symm))
  linear_combination -hlim

/-! ### Weight-two invariance of `c + G2` -/

/-- The candidate weight-two function `c + G2`. -/
def F : ℍ → ℂ := fun τ => finitePart τ + EisensteinSeries.G2 τ

theorem F_slash_T : F ∣[(2 : ℤ)] T = F := by
  funext τ
  have hd : UpperHalfPlane.denom T τ = 1 := by
    rw [ModularGroup.denom_apply]; simp [ModularGroup.coe_T]
  have hG := congrFun EisensteinSeries.G2_T_transform τ
  rw [ModularForm.SL_slash_apply, hd] at hG ⊢
  simp only [one_zpow, mul_one] at hG ⊢
  simp only [F, finitePart_T, hG]

theorem F_slash_S : F ∣[(2 : ℤ)] S = F := by
  funext τ
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hG := EisensteinSeries.G2_S_transform τ
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S]
  simp only [F, finitePart_S]
  have hG' : EisensteinSeries.G2 (S • τ) = (τ : ℂ) ^ 2 * EisensteinSeries.G2 τ - 2 * π * I * τ := by
    rw [hG]; field_simp; ring
  rw [hG']
  field_simp
  ring

/-- **`c + G2` is invariant under the weight-two action of `SL(2, ℤ)`.** -/
theorem F_slash (γ : SL(2, ℤ)) : F ∣[(2 : ℤ)] γ = F := by
  have hg : γ ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact F_slash_S
    · exact F_slash_T
  | one => exact SlashAction.slash_one _ _
  | mul x y _ _ hx hy => rw [SlashAction.slash_mul, hx, hy]
  | inv x _ hx =>
    have h := congrArg (fun f => f ∣[(2 : ℤ)] x⁻¹) hx
    simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at h
    exact h.symm

end ZInQ.Contrib.HeckePrimeRationality.ThetaG2
