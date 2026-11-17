/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_mul_thetaL_eq_qExpansion_of_finiteIndex (git blob f1b48813a7228ed9e3f723e3b65110eeb7bba4ff, sha256 90789c8b6219a0253a855ee35cd89a6bfc6785902cd98ac7d10afaeed7e27a0b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpansionDiff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_exists_rankinCohen_one_qExpansion_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace UpperHalfPlane
end UpperHalfPlane
namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_mul_thetaL_eq_qExpansion_of_finiteIndex

open _root_.UpperHalfPlane
open _root_.ModularCurve hiding coeffEmb_jq
open scoped MatrixGroups

noncomputable section

namespace Sol_HOL_finiteIndex

theorem thetaL_coeff {L : Type*} [Field L] (x : LaurentSeries L) (n : ℤ) :
    (thetaL L x).coeff n = (n : L) * x.coeff n := by
  rw [thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp only [Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

theorem support_thetaL_subset {L : Type*} [Field L] (x : LaurentSeries L) :
    (thetaL L x).support ⊆ x.support := by
  intro n hn
  rw [HahnSeries.mem_support, thetaL_coeff] at hn
  rw [HahnSeries.mem_support]
  exact right_ne_zero_of_mul hn

theorem thetaL_mul {L : Type*} [Field L] (x y : LaurentSeries L) :
    thetaL L (x * y) = thetaL L x * y + x * thetaL L y := by
  ext n
  rw [HahnSeries.coeff_add, thetaL_coeff,
    HahnSeries.coeff_mul_left' x.isPWO_support (support_thetaL_subset x),
    HahnSeries.coeff_mul_right' y.isPWO_support (support_thetaL_subset y),
    HahnSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [thetaL_coeff, thetaL_coeff, ← hij.2.2, Int.cast_add]
  ring

theorem thetaL_C {L : Type*} [Field L] (r : L) : thetaL L (HahnSeries.C r) = 0 := by
  ext n
  rw [thetaL_coeff, HahnSeries.C_apply, HahnSeries.coeff_single, HahnSeries.coeff_zero]
  split_ifs with hn
  · rw [hn, Int.cast_zero, zero_mul]
  · exact mul_zero _

theorem thetaL_coe {L : Type*} [Field L] (p : PowerSeries L) :
    thetaL L (p : LaurentSeries L) =
      ((PowerSeries.mk fun n : ℕ => (n : L) * PowerSeries.coeff n p : PowerSeries L) :
        LaurentSeries L) := by
  ext n
  rw [thetaL_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · exact mul_zero _
  · rw [PowerSeries.coeff_mk]
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp h)
    simp





theorem ofNat_laurent_ne_zero (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : LaurentSeries ℂ) ≠ 0 := by
  rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := ℂ)) n]
  exact HahnSeries.C_ne_zero (OfNat.ofNat_ne_zero n)

theorem D_ne_zero : ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
  intro h
  have h1 := ModularForm.discriminant_qExpansion_coeff_one
  have h0 : qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) = 0 :=
    HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

theorem E4_ne_zero : ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
  intro h
  have h1 : PowerSeries.coeff 0 (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  have h0 : qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) = 0 :=
    HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

theorem E6_ne_zero : ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
  intro h
  have h1 : PowerSeries.coeff 0 (qExpansion 1 (ModularForm.E₆ : ℍ → ℂ)) = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩
  have h0 : qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) = 0 :=
    HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

theorem discr_laurent : 1728 * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 - ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 2 := by
  have hfun : (1728 : ℂ) • (ModularForm.discriminant : ℍ → ℂ) =
      ⇑(ModularForm.E₄.pow 3) - ⇑(ModularForm.E₆.pow 2) := by
    ext z
    simp only [Pi.smul_apply, Pi.sub_apply, ModularForm.coe_pow, Pi.pow_apply, smul_eq_mul,
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  have hps : (1728 : ℂ) • qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) =
      qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) ^ 3 - qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) ^ 2 := by
    rw [← CuspForm.coe_discriminant,
      ← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, CuspForm.coe_discriminant,
      hfun, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hL := congrArg ((↑) : PowerSeries ℂ → LaurentSeries ℂ) hps
  simp only [PowerSeries.coe_smul, PowerSeries.coe_sub, PowerSeries.coe_pow] at hL
  rw [← HahnSeries.C_mul_eq_smul, map_ofNat] at hL
  exact hL

theorem rankinCohen_laurent :
    4 * ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) * thetaL ℂ ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) - 6 * thetaL ℂ ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) * ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = -3456 * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  have hT : ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ :=
    (MonoidHom.range_eq_map _).symm
  have h1 : (1 : ℝ) ∈ ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [hT]; exact one_mem_strictPeriods_SL
  obtain ⟨B, -, hB⟩ := ModularForm.exists_rankinCohen_one_qExpansion_eq h1
    (ModularForm.E₄.mcast rfl hT) (ModularForm.E₆.mcast rfl hT)
  simp only [ModularForm.coe_mcast, Int.cast_ofNat] at hB
  set B' : ModularForm 𝒮ℒ 12 := B.mcast (by norm_num) hT.symm with hB'def
  have hBB' : (B' : ℍ → ℂ) = B := rfl
  have h0 : (qExpansion 1 (B' : ℍ → ℂ)).coeff 0 = 0 := by
    rw [hBB', hB]
    simp
  obtain ⟨c, hc⟩ :=
    CuspForm.exists_smul_discriminant_of_weight_eq_twelve (ModularForm.toCuspForm B' h0)
  have hcfun : (B : ℍ → ℂ) = c • ⇑CuspForm.discriminant := by
    rw [← CuspForm.IsGLPos.coe_smul, hc]; rfl
  have hqB : qExpansion 1 (B : ℍ → ℂ) =
      c • qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) := by
    rw [hcfun, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      CuspForm.coe_discriminant]
  have hkey := hB.symm.trans hqB
  have hc1 : c = -3456 := by
    have h := congrArg (PowerSeries.coeff 1) hkey
    norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, PowerSeries.coeff_mk,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩,
      ModularForm.E₄_qExpansion_coeff_one, ModularForm.E₆_qExpansion_coeff_one,
      ModularForm.discriminant_qExpansion_coeff_one] at h
    exact h.symm
  rw [hc1] at hkey
  have hL := congrArg ((↑) : PowerSeries ℂ → LaurentSeries ℂ) hkey
  rw [thetaL_coe, thetaL_coe]
  simp only [PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_smul, map_ofNat] at hL
  rw [hL, ← HahnSeries.C_mul_eq_smul, map_neg, map_ofNat]

theorem coeffEmb_jq : coeffEmb ℂ jq = ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  rw [← ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant,
    ← map_jqModC (algebraMap ℚ ℂ), jqModC_rat]
  rfl

theorem thetaL_j_mul_D : thetaL ℂ (coeffEmb ℂ jq) * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = -(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 2 * ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by
  have hD := D_ne_zero
  have hRC := rankinCohen_laurent
  have hΔ := discr_laurent
  have hj := coeffEmb_jq

  have hC : coeffEmb ℂ jq * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 := by rw [hj, div_mul_cancel₀ _ hD]

  have hA := congrArg (thetaL ℂ) hC
  rw [thetaL_mul, pow_succ, thetaL_mul, pow_two, thetaL_mul] at hA
  have hB := congrArg (thetaL ℂ) hΔ
  rw [thetaL_mul, map_sub, pow_succ, thetaL_mul, pow_two, thetaL_mul, pow_two, thetaL_mul]
    at hB

  have hθ1728 : thetaL ℂ (1728 : LaurentSeries ℂ) = 0 := by
    rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := ℂ)) 1728]
    exact thetaL_C _
  rw [hθ1728, zero_mul, zero_add] at hB
  apply mul_right_cancel₀ (mul_ne_zero (ofNat_laurent_ne_zero 3456) hD)
  linear_combination (3456 * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) * hA - (2 * coeffEmb ℂ jq * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) * hB
    - (2 * (3 * ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 2 * thetaL ℂ ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) - 2 * ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) * thetaL ℂ ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))) * hC
    + (6 * ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 2 * thetaL ℂ ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) * hΔ + (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 2 * ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) * hRC

end Sol_HOL_finiteIndex

open Sol_HOL_finiteIndex in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) (Y : LaurentSeries ℂ)
    (hY : Y * thetaL ℂ (coeffEmb ℂ jq) =
      ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) :
    IsIntegral (Algebra.adjoin ℂ ({coeffEmb ℂ jq} : Set (LaurentSeries ℂ)))
      (Y ^ 6 * coeffEmb ℂ jq ^ 4 * (coeffEmb ℂ jq - 1728) ^ 3) := by

  set e4 := ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) with he4
  set e6 := ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) with he6
  set d := ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
    with hd
  set F := ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) with hF
  have hD : d ≠ 0 := D_ne_zero
  have h4 : e4 ≠ 0 := E4_ne_zero
  have h6 : e6 ≠ 0 := E6_ne_zero
  have hj : coeffEmb ℂ jq = e4 ^ 3 / d := coeffEmb_jq
  have hθ : thetaL ℂ (coeffEmb ℂ jq) * d = -(e4 ^ 2 * e6) := thetaL_j_mul_D
  have hΔ : 1728 * d = e4 ^ 3 - e6 ^ 2 := discr_laurent

  have hY' : Y * (e4 ^ 2 * e6) = -(F * d) := by
    have h := congrArg (· * d) hY
    simp only [mul_assoc] at h
    linear_combination Y * hθ - h
  have hYv : Y = -(F * d) / (e4 ^ 2 * e6) := by
    rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ h4) h6)]; exact hY'
  have hJ' : coeffEmb ℂ jq - 1728 = e6 ^ 2 / d := by
    rw [hj, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]
    linear_combination -hΔ

  have hEq : Y ^ 6 * coeffEmb ℂ jq ^ 4 * (coeffEmb ℂ jq - 1728) ^ 3 = F ^ 6 / d := by
    rw [hJ', hYv, hj]
    field_simp

  have h1N := h1
  set fM : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2 :=
    ModularFormClass.modularForm f with hfM
  set F6 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
    (fM.pow 6).mcast (by norm_num) with hF6
  have hF6q : qExpansion 1 (F6 : ℍ → ℂ) = (qExpansion 1 (f : ℍ → ℂ)) ^ 6 := by
    show qExpansion 1 ⇑(fM.pow 6) = _
    rw [ModularForm.qExpansion_pow one_pos h1N]
    rfl
  have hF6L : ((qExpansion 1 (F6 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = F ^ 6 := by
    rw [hF6q, PowerSeries.coe_pow]
  have hI := ModularForm.isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic
    (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ))) h1N 1 (k := 12)
    (by norm_num) F6
  rw [pow_one, hF6L] at hI
  rw [hEq, hj]
  exact hI

end

#print axioms solution
