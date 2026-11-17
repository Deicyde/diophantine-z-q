/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_multiplier_eq_exp_of_periodAlongOf_add_petersson_mem_periodLatticeOf (git blob a6f352720cb5b5077ee0e30c88cae8a2afdeb9b8, sha256 ae0f3d3c2ec6f18cb1bca05a551b211e75fe1e505f86c11498746be3a64c9109).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_periodAlongOf_add_petersson_mem_periodLatticeOf_of_multiplier_eq_exp
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_multiplier_eq_exp_of_periodAlongOf_add_petersson_mem_periodLatticeOf

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology ComplexConjugate

namespace ModularCurve
export _root_.ModularCurve (periodAlongOf periodOf periodLatticeOf period periodAlongOf_add_petersson_mem_periodLatticeOf_of_multiplier_eq_exp exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one petersson_mem_periodLatticeOf_iff_re_periodOf_int)
namespace ReciprocityThirdFirstAssemblyOf
open _root_.ModularCurve

abbrev FS (Γ : Subgroup SL(2, ℤ)) : Set ℍ :=
  FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

theorem integrable_petersson (f g : CuspForm Γ 2) :
    Integrable (petersson 2 f g) (volume.restrict (FS Γ)) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left 2 ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) f g
  have hcont : Continuous (petersson 2 f g) :=
    petersson_continuous 2 (CuspFormClass.holo f).continuous (CuspFormClass.holo g).continuous
  haveI : IsFiniteMeasure (volume.restrict (FS Γ)) :=
    isFiniteMeasure_restrict.mpr (FLT.Gamma0FundamentalSet.volume_gammaFundamentalSet_lt_top Γ).ne
  exact Integrable.of_bound hcont.aestronglyMeasurable C (ae_of_all _ hC)

omit [Γ.FiniteIndex] in

theorem petersson_sub_left_apply (f k g : CuspForm Γ 2) (τ : ℍ) :
    petersson 2 (⇑(f - k)) g τ = petersson 2 f g τ - petersson 2 k g τ := by
  simp only [petersson, CuspForm.coe_sub, Pi.sub_apply, map_sub]
  ring

theorem integral_petersson_sub_left (f k g : CuspForm Γ 2) :
    (∫ τ in FS Γ, petersson 2 (⇑(f - k)) g τ) =
      (∫ τ in FS Γ, petersson 2 f g τ) - ∫ τ in FS Γ, petersson 2 k g τ := by
  rw [← integral_sub (integrable_petersson f g) (integrable_petersson k g)]
  congr 1
  funext τ
  exact petersson_sub_left_apply f k g τ

omit [Γ.FiniteIndex] in

theorem cexp_two_pi_I_intCast (m : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)) = 1 := by
  rw [show (2 * Real.pi * Complex.I * (m : ℂ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

end ModularCurve.ReciprocityThirdFirstAssemblyOf

open ModularCurve.ReciprocityThirdFirstAssemblyOf in
open Classical in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (χ : Γ → ℂ) (f : CuspForm Γ 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : Γ, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, ∃ n : ℤ,
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
        2 * n = (Nat.card (MulAction.stabilizer Γ τ) : ℤ) *
          c.sum (fun τ' m =>
            if ∃ γ : Γ, (γ : SL(2, ℤ)) • τ' = τ then m else 0))
    (hf : ∃ Λ ∈ ModularCurve.periodLatticeOf Γ, ∀ g : CuspForm Γ 2,
      (c.sum fun τ n => n • ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ) g +
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
          UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = Λ g) :
    ∀ γ : Γ,
      χ γ = Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ f).re : ℂ)) := by

  obtain ⟨k, hk⟩ :=
    ModularCurve.exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one Γ hneg hΓ c F χ hF hχ hunit hcusp hord

  have hχ' : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ := by
    intro γ τ
    rw [hχ γ τ, hk γ]
  obtain ⟨Λ₁, hΛ₁, h₁⟩ :=
    ModularCurve.periodAlongOf_add_petersson_mem_periodLatticeOf_of_multiplier_eq_exp
      Γ hneg c F k hF hχ' hcusp hord
  obtain ⟨Λ, hΛ, h⟩ := hf

  have hmem : ∃ Λ' ∈ ModularCurve.periodLatticeOf Γ, ∀ g : CuspForm Γ 2,
      Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
        UpperHalfPlane.petersson 2 (⇑(f - k)) ⇑g τ) = Λ' g := by
    refine ⟨Λ - Λ₁, sub_mem hΛ hΛ₁, fun g => ?_⟩
    have e1 := h g
    have e2 := h₁ g
    rw [LinearMap.sub_apply, ← e1, ← e2]
    change Complex.I * (∫ τ in FS Γ, petersson 2 (⇑(f - k)) g τ) = _
    rw [integral_petersson_sub_left f k g]
    change Complex.I * ((∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, petersson 2 f g τ) -
        ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, petersson 2 k g τ) = _
    ring

  intro γ
  obtain ⟨m, hm⟩ :=
    (ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int Γ hΓ hneg (f - k)).mp hmem γ
  have hre : (ModularCurve.periodOf Γ γ f).re = (ModularCurve.periodOf Γ γ k).re + (m : ℝ) := by
    rw [map_sub, Complex.sub_re] at hm
    linarith
  rw [hk γ, hre]
  push_cast
  rw [mul_add, Complex.exp_add, cexp_two_pi_I_intCast m, mul_one]
