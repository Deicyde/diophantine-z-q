/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PrimCosetReps
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow.ModularCurve Complex"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qTwist qTwist_coeff cosetSubst"
namespace CosetQParamAux
p2m_open "ModularCurve"

theorem qParam_coset {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (τ : ℂ) :
    Function.Periodic.qParam 1 ((a * τ + b) / d)
      = Complex.exp (2 * Real.pi * Complex.I / N) ^ (a * b) * Function.Periodic.qParam N τ ^ (a * a) := by
  have hd0 : (d : ℂ) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; exact hN (by simpa using had.symm)
    exact_mod_cast this
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have hNad : (N : ℂ) = a * d := by exact_mod_cast had.symm
  have ha0 : (a : ℂ) ≠ 0 := by
    have : a ≠ 0 := by rintro rfl; exact hN (by simpa using had.symm)
    exact_mod_cast this
  push_cast
  rw [hNad]
  field_simp
  ring

end ModularCurve.CosetQParamAux

open ModularCurve.CosetQParamAux UpperHalfPlane in
theorem solution {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N)
    [NeZero a] (ζ : ℂˣ) (hζ : (ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N))
    (S : LaurentSeries ℂ) (τ : ℂ) (x : ℂ)
    (h : HasSum (fun m : ℤ => S.coeff m * Function.Periodic.qParam 1 ((a * τ + b) / d) ^ m) x) :
    HasSum (fun m : ℤ => (ModularCurve.cosetSubst ζ a b S).coeff m * Function.Periodic.qParam N τ ^ m) x := by
  haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne a)⟩
  set t : ℂ := Function.Periodic.qParam N τ with ht
  set u : ℂˣ := ζ ^ (a * b) with hu
  rw [qParam_coset hN had τ, ← hζ, ← ht] at h

  have hinj : Function.Injective (fun m : ℤ => ((a * a : ℕ) : ℤ) * m) :=
    mul_right_injective₀ (by exact_mod_cast (NeZero.ne (a * a)))
  refine (Function.Injective.hasSum_iff hinj ?_).mp ?_
  · intro k hk
    have hnd : ¬ ((a * a : ℕ) : ℤ) ∣ k := by
      rintro ⟨c, rfl⟩
      exact hk ⟨c, rfl⟩
    show ((qExpand ℂ (a * a)) (qTwist (ζ ^ (a * b)) S)).coeff k * t ^ k = 0
    rw [qExpand_coeff_of_not_dvd (a * a) _ hnd, zero_mul]
  · have hcomp : ((fun m : ℤ => (ModularCurve.cosetSubst ζ a b S).coeff m * t ^ m) ∘
        (fun m : ℤ => ((a * a : ℕ) : ℤ) * m))
        = fun m : ℤ => S.coeff m * ((ζ : ℂ) ^ (a * b) * t ^ (a * a)) ^ m := by
      funext m
      simp only [Function.comp_apply]
      show ((qExpand ℂ (a * a)) (qTwist (ζ ^ (a * b)) S)).coeff (((a * a : ℕ) : ℤ) * m) * t ^ _ = _
      rw [qExpand_coeff_mul, qTwist_coeff, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, mul_zpow,
        zpow_mul, zpow_natCast]
      ring
    rw [hcomp]
    exact h

end
