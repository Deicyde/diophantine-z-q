/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion_of_gamma_le (git blob 0e7da17b629b94982a014d63c9a9e4f318a7d0c9, sha256 d43981289ba7f50331ca75c7263a295069d60575c4bc2870b87f1f0dbd043444).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpansionDiff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_isIntegral_adjoin_of_isIntegral_adjoin_coeffMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_of_mul_thetaL_eq_qExpansion_of_gamma_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion_of_gamma_le

open UpperHalfPlane ModularCurve AlgebraicCurve

namespace Sol

theorem thetaL_coeff' {L : Type*} [Field L] (x : LaurentSeries L) (n : ℤ) :
    (thetaL L x).coeff n = (n : L) * x.coeff n := by
  rw [thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp only [Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

theorem coeffMap_thetaL {L₁ L₂ : Type*} [Field L₁] [Field L₂] (σ : L₁ →+* L₂)
    (x : LaurentSeries L₁) :
    coeffMap σ (thetaL L₁ x) = thetaL L₂ (coeffMap σ x) := by
  ext n
  simp only [coeffMap_coeff, thetaL_coeff', map_mul, map_intCast]

theorem coeffMap_coeffEmb' {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra ℚ L₁] [Algebra ℚ L₂]
    (σ : L₁ →+* L₂) (x : LaurentSeries ℚ) :
    coeffMap σ (coeffEmb L₁ x) = coeffEmb L₂ x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap,
    Subsingleton.elim (σ.comp (algebraMap ℚ L₁)) (algebraMap ℚ L₂)]

theorem ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (f : F)
    (n : ℕ) : v.ord (f ^ n) = (n : ℤ) * v.ord f := by
  rw [← zpow_natCast, Place.ord_zpow]

end Sol

open scoped MatrixGroups in
open Sol in
theorem solution
    (F : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (j : ↥F) (hj : (j : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq)
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ)
    (h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (σ : AlgebraicClosure ℚ →+* ℂ) (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ↥F) (hy0 : y ≠ 0)
    (hy : coeffMap σ ((y : LaurentSeries (AlgebraicClosure ℚ)) *
        thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
      ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (w : Place (AlgebraicClosure ℚ) ↥F) (hw : w.ord j < 0) :
    1 - w.ord j ≤ w.ord y := by

  set K := AlgebraicClosure ℚ with hK
  set jb : F := j with hjb_def
  let c : F := algebraMap K F 1728

  have hj0 : jb ≠ 0 := fun h => by rw [h, Place.ord_zero] at hw; exact lt_irrefl _ hw
  have hc0 : c ≠ 0 := by
    show algebraMap K F 1728 ≠ 0
    rw [map_ne_zero_iff _ (algebraMap K F).injective]; norm_num
  have hjc0 : jb - c ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h, Place.ord_algebraMap] at hw
    exact lt_irrefl _ hw

  have hjc : w.ord (jb - c) ≤ w.ord jb := by
    have h := Place.min_ord_le_ord_add w hjc0 hc0 (by rwa [sub_add_cancel])
    rw [sub_add_cancel, Place.ord_algebraMap] at h
    omega
  have ht : 0 ≤ w.ord jb⁻¹ := by rw [Place.ord_inv]; omega

  set u : F := y ^ (2 * M) * jb ^ (M + 1) * (jb - c) ^ M with hu
  have hI := ModularCurve.isIntegral_adjoin_coeffEmb_jq_inv_of_mul_thetaL_eq_qExpansion_of_gamma_le M Γ hΓ h1 f
    (coeffMap σ (y : LaurentSeries K)) (by
      rw [← coeffMap_coeffEmb' σ, ← coeffMap_thetaL, ← map_mul, hy])
  have hD : IsIntegral
      (Algebra.adjoin K ({((jb⁻¹ : F) : LaurentSeries K)} : Set (LaurentSeries K)))
      (u : LaurentSeries K) := by
    refine isIntegral_adjoin_of_isIntegral_adjoin_coeffMap σ _ _ ?_
    have hcoe : ((u : F) : LaurentSeries K) =
        (y : LaurentSeries K) ^ (2 * M) * coeffEmb K jq ^ (M + 1) * (coeffEmb K jq - 1728) ^ M := by
      show F.val u = _
      simp only [hu, c, map_mul, map_pow, map_sub, map_ofNat]
      rw [← hj]
      rfl
    have hj : ((jb⁻¹ : F) : LaurentSeries K) = (coeffEmb K jq)⁻¹ := by
      show F.val jb⁻¹ = _
      rw [map_inv₀]
      exact congrArg _ hj
    rw [hcoe, hj, map_mul, map_mul, map_pow, map_pow, map_pow, map_sub, map_inv₀,
      coeffMap_coeffEmb', map_ofNat]
    exact hI
  have hu0 : 0 ≤ w.ord u :=
    Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg w
      (by first | exact isIntegral_adjoin_intermediateField_mk F (jb⁻¹).2 u.2 hD
                | simpa using isIntegral_adjoin_intermediateField_mk F (jb⁻¹).2 u.2 hD) ht

  have hA : y ^ (2 * M) * jb ^ (M + 1) ≠ 0 := mul_ne_zero (pow_ne_zero _ hy0) (pow_ne_zero _ hj0)
  have hB : (jb - c) ^ M ≠ 0 := pow_ne_zero _ hjc0
  rw [hu, w.ord_mul hA hB, w.ord_mul (pow_ne_zero _ hy0) (pow_ne_zero _ hj0), ord_pow',
    ord_pow', ord_pow'] at hu0
  push_cast at hu0
  have hN : (1 : ℤ) ≤ M := by exact_mod_cast NeZero.one_le
  by_contra hlt
  push Not at hlt
  have h1' : (M : ℤ) * w.ord y ≤ (M : ℤ) * (-w.ord jb) :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  have h2 : (M : ℤ) * w.ord (jb - c) ≤ (M : ℤ) * w.ord jb :=
    mul_le_mul_of_nonneg_left hjc (by positivity)
  linarith

#print axioms solution
