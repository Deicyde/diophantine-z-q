/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt (git blob cc4cdab63eb938cac8b88f3dcba61c1fe2179bd2, sha256 6a4502ec40cb0ea742b08590dedb5e8254e67f32acd0d665aa7b0035cadaab07).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_TateLocalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt

set_option Elab.async false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

namespace TwistedUnramifiedLocal

open LanglandsTunnell.TateLocal NumberField.AdelicLevel Filter Topology

section Auxiliary

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem modulus_eq_of_valued_eq {x y : v.adicCompletion F} (h : Valued.v x = Valued.v y) :
    modulus x = modulus y := by
  apply NNReal.eq
  rw [modulus_adicCompletion_eq_nnnorm F v x, modulus_adicCompletion_eq_nnnorm F v y, coe_nnnorm,
    coe_nnnorm, NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, h]

private theorem charExt_inv_eq_of_valued_eq (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    {x y : v.adicCompletion F} (hx : x ≠ 0) (hy : y ≠ 0) (h : Valued.v x = Valued.v y) :
    charExt χ⁻¹ x = charExt χ⁻¹ y := by
  have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  have hu : Valued.v ((Units.mk0 x hx * (Units.mk0 y hy)⁻¹ : (v.adicCompletion F)ˣ)
      : v.adicCompletion F) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, map_mul, map_inv₀, h,
      mul_inv_cancel₀ hvy]
  have hχeq : χ (Units.mk0 x hx) = χ (Units.mk0 y hy) := by
    have h1 := hχ _ hu
    rwa [map_mul, map_inv, mul_inv_eq_one] at h1
  rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hy, MonoidHom.inv_apply, MonoidHom.inv_apply,
    hχeq]

private noncomputable def untwisted (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (x : v.adicCompletion F) : ℂ :=
  (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
    + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x

private theorem untwisted_of_le (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) {x : v.adicCompletion F}
    (hx : Valued.v x ≤ 1) : untwisted χ s x = 1 := by
  have hmem : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hx
  have hnot : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := fun h => h hmem
  rw [untwisted, Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot, add_zero]

private theorem untwisted_of_lt (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) {x : v.adicCompletion F}
    (hx : 1 < Valued.v x) :
    untwisted χ s x = charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (-(2 * s + 1)) := by
  have hnot : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := fun h => not_le.mpr hx h
  have hmem : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := hnot
  rw [untwisted, Set.indicator_of_notMem hnot, Set.indicator_of_mem hmem, zero_add]

private theorem untwisted_add_of_lt (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1) (s : ℂ)
    {t x : v.adicCompletion F} (htx : Valued.v t < Valued.v x) (hx : 1 < Valued.v x) :
    untwisted χ s (t + x) = untwisted χ s x := by
  have hv : Valued.v (t + x) = Valued.v x := Valuation.map_add_eq_of_lt_right _ htx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact WithZero.not_lt_zero _ hx
  have htx0 : t + x ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact hx0 ((Valuation.zero_iff _).mp hv.symm)
  rw [untwisted_of_lt χ s (hv ▸ hx), untwisted_of_lt χ s hx,
    charExt_inv_eq_of_valued_eq χ hχ htx0 hx0 hv, modulus_eq_of_valued_eq hv]

private theorem untwisted_add_of_le_one (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1) (s : ℂ)
    {t : v.adicCompletion F} (ht : Valued.v t ≤ 1) (x : v.adicCompletion F) :
    untwisted χ s (t + x) = untwisted χ s x := by
  by_cases hx : Valued.v x ≤ 1
  · have htx : Valued.v (t + x) ≤ 1 := (Valuation.map_add_le_max' _ t x).trans (max_le ht hx)
    rw [untwisted_of_le χ s htx, untwisted_of_le χ s hx]
  · rw [not_le] at hx
    exact untwisted_add_of_lt χ hχ s (lt_of_le_of_lt ht hx) hx

end Auxiliary

end TwistedUnramifiedLocal

open TwistedUnramifiedLocal LanglandsTunnell.TateLocal NumberField.AdelicLevel Filter Topology in

theorem solution
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (ξ : v.adicCompletion F) (hξ : WithZero.exp n < Valued.v ξ) :
    ∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
          * ψ (-(ξ * x))) ∂μ
      = 0 := by
  have _ := hϖ
  have _ := hs
  have _ := hψn
  obtain ⟨x₀, hx₀, hne⟩ := hψn'
  have hξ0 : Valued.v ξ ≠ 0 := by
    intro h
    rw [h] at hξ
    exact WithZero.not_lt_zero _ hξ
  have hξne : ξ ≠ 0 := (Valuation.ne_zero_iff _).mp hξ0
  have hξ1 : WithZero.exp (n + 1) ≤ Valued.v ξ := by
    rw [← WithZero.exp_log hξ0] at hξ ⊢
    rw [WithZero.exp_lt_exp] at hξ
    exact WithZero.exp_le_exp.mpr (by omega)
  set t : v.adicCompletion F := -(ξ⁻¹ * x₀) with ht_def
  have hξt : -(ξ * t) = x₀ := by rw [ht_def, mul_neg, neg_neg, mul_inv_cancel_left₀ hξne]
  have ht1 : Valued.v t ≤ 1 := by
    rw [ht_def, Valuation.map_neg, map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.mpr hξ0), mul_one]
    exact hx₀.trans hξ1
  have hpt : ∀ x, untwisted χ s (t + x) * ψ (-(ξ * (t + x))) = ψ x₀ * (untwisted χ s x * ψ (-(ξ * x))) := by
    intro x
    rw [untwisted_add_of_le_one χ hχ s ht1 x, mul_add, neg_add, AddChar.map_add_eq_mul, hξt]
    ring
  have htrans : ∫ x, untwisted χ s x * ψ (-(ξ * x)) ∂μ = ψ x₀ * ∫ x, untwisted χ s x * ψ (-(ξ * x)) ∂μ := by
    calc ∫ x, untwisted χ s x * ψ (-(ξ * x)) ∂μ
        = ∫ x, untwisted χ s (t + x) * ψ (-(ξ * (t + x))) ∂μ :=
          (integral_add_left_eq_self (fun x => untwisted χ s x * ψ (-(ξ * x))) t).symm
      _ = ∫ x, ψ x₀ * (untwisted χ s x * ψ (-(ξ * x))) ∂μ := by simp_rw [hpt]
      _ = ψ x₀ * ∫ x, untwisted χ s x * ψ (-(ξ * x)) ∂μ := integral_const_mul _ _
  have h1ne : (1 : ℂ) - ψ x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hprod : ((1 : ℂ) - ψ x₀) * ∫ x, untwisted χ s x * ψ (-(ξ * x)) ∂μ = 0 := by
    rw [sub_mul, one_mul, ← htrans, sub_self]
  show ∫ x, untwisted χ s x * ψ (-(ξ * x)) ∂μ = 0
  exact (mul_eq_zero.mp hprod).resolve_left h1ne
