/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm (git blob 7a8bb469318d0b4f1e71f07a632891a22afa4740, sha256 52dd8425f4c6b77660df53462b9986033fc0768068fd5e525be1ef10a4eb223a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm.ModularCurve
end P2MW.S_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm.ModularCurve
namespace P2MW.S_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm.ModularCurve.ESPrincipalAssembly
end P2MW.S_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm.ModularCurve.ESPrincipalAssembly

namespace P2MW.S_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm

set_option autoImplicit false

open scoped MatrixGroups

namespace ModularCurve
export _root_.ModularCurve (Period.parabolicHoms six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma)
namespace ESPrincipalAssembly
open _root_.ModularCurve

open ModularCurve.Period CongruenceSubgroup

theorem trace_T_sq : ((ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [Matrix.trace_fin_two]
  simp [ModularGroup.T]

theorem trace_neg_one_sq : ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [Matrix.trace_fin_two]
  simp

theorem S_mul_S : (ModularGroup.S : SL(2, ℤ)) * ModularGroup.S = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]

def toGammaOne (g : SL(2, ℤ)) : Gamma 1 :=
  ⟨g, by simp [CongruenceSubgroup.Gamma_one_top]⟩

@[scoped simp]
theorem coe_toGammaOne (g : SL(2, ℤ)) : ((toGammaOne g : Gamma 1) : SL(2, ℤ)) = g := rfl

theorem toGammaOne_mul (g h : SL(2, ℤ)) : toGammaOne (g * h) = toGammaOne g * toGammaOne h := rfl

theorem toGammaOne_one : toGammaOne 1 = 1 := rfl

theorem toGammaOne_inv (g : SL(2, ℤ)) : toGammaOne g⁻¹ = (toGammaOne g)⁻¹ := rfl

theorem toGammaOne_coe (γ : Gamma 1) : toGammaOne (γ : SL(2, ℤ)) = γ := by
  ext; rfl

theorem eq_zero_of_mem_parabolicHoms_gamma_one (φ : Additive (Gamma 1) →+ ℤ)
    (hφ : φ ∈ parabolicHoms ℤ (Gamma 1) ℤ) : φ = 0 := by
  rw [mem_parabolicHoms_iff] at hφ

  let ψ : SL(2, ℤ) → ℤ := fun g => φ (Additive.ofMul (toGammaOne g))
  have hψ_mul : ∀ g h, ψ (g * h) = ψ g + ψ h := by
    intro g h
    simp only [ψ, toGammaOne_mul, ofMul_mul, map_add]
  have hψ_one : ψ 1 = 0 := by
    simp only [ψ, toGammaOne_one, ofMul_one, map_zero]
  have hψ_inv : ∀ g, ψ g⁻¹ = -ψ g := by
    intro g
    have h := hψ_mul g g⁻¹
    rw [mul_inv_cancel, hψ_one] at h
    omega

  have hT : ψ ModularGroup.T = 0 := hφ (toGammaOne ModularGroup.T) trace_T_sq

  have hneg : ψ (-1) = 0 := hφ (toGammaOne (-1)) trace_neg_one_sq

  have hS : ψ ModularGroup.S = 0 := by
    have h := hψ_mul ModularGroup.S ModularGroup.S
    rw [S_mul_S, hneg] at h
    omega

  have hall : ∀ g : SL(2, ℤ), ψ g = 0 := by
    intro g
    have hg : g ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
      rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
        rcases hx with rfl | rfl
        · exact hS
        · exact hT
    | one => exact hψ_one
    | mul x y _ _ hx hy => rw [hψ_mul, hx, hy, add_zero]
    | inv x _ hx => rw [hψ_inv, hx, neg_zero]
  ext γ
  have h := hall (Additive.toMul γ : Gamma 1)
  simp only [ψ, toGammaOne_coe, ofMul_toMul] at h
  simp at h ⊢
  exact h

theorem parabolicHoms_gamma_one_eq_bot : parabolicHoms ℤ (Gamma 1) ℤ = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [Submodule.mem_bot]
  exact eq_zero_of_mem_parabolicHoms_gamma_one φ hφ

theorem finrank_parabolicHoms_gamma_one : Module.finrank ℤ (parabolicHoms ℤ (Gamma 1) ℤ) = 0 := by
  rw [parabolicHoms_gamma_one_eq_bot, finrank_bot]

theorem main_of_two_le (N : ℕ) (hN : 2 ≤ N) :
    Module.finrank ℤ (parabolicHoms ℤ (Gamma N) ℤ) ≤ 2 * Module.finrank ℂ (CuspForm (Gamma N) 2) := by
  have hA := ModularCurve.six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq N hN
  have hG := ModularCurve.twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma N hN
  set r := Module.finrank ℤ (parabolicHoms ℤ (Gamma N) ℤ)
  set d := Module.finrank ℂ (CuspForm (Gamma N) 2)
  set μ := (Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index
  have h1 : 6 * N * r + 6 * μ ≤ 12 * N * d + 6 * μ := hA ▸ hG
  have h2 : 6 * N * r ≤ 6 * N * (2 * d) := by
    have h3 : 6 * N * r ≤ 12 * N * d := Nat.le_of_add_le_add_right h1
    calc 6 * N * r ≤ 12 * N * d := h3
      _ = 6 * N * (2 * d) := by ring
  have hpos : 0 < 6 * N := by omega
  exact Nat.le_of_mul_le_mul_left h2 hpos

end ModularCurve.ESPrincipalAssembly
open scoped _root_.P2MW.S_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm.ModularCurve _root_.P2MW.S_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm.ModularCurve.ESPrincipalAssembly
open scoped _root_.P2MW.S_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm.ModularCurve

open ModularCurve.ESPrincipalAssembly in

theorem solution (N : ℕ) [NeZero N] :
    Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma N) ℤ) ≤
      2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) := by
  rcases Nat.lt_or_ge N 2 with h | h
  · obtain rfl : N = 1 := by
      have h0 : N ≠ 0 := NeZero.ne N
      omega
    rw [finrank_parabolicHoms_gamma_one]
    exact Nat.zero_le _
  · exact main_of_two_le N h
