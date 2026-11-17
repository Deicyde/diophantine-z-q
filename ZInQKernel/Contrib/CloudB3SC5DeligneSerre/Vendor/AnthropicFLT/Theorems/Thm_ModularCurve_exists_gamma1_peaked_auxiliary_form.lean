/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_gamma1_peaked_auxiliary_form (git blob 906bb16c0b287f37eb6627cf3fd390cc1502786e, sha256 5d1b804ac66c7d71dce830468df4e7614ca23fe0969127adef64f38dba8d7dea).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_gamma1_peaked_auxiliary_form

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_gamma1_peaked_auxiliary_form (N : ℕ) (hN : 2 ≤ N) (k : ℤ)
    (hk : Odd k → 3 ≤ N) :
    ∃ (w : ℤ) (m₀ a : ℕ) (δ : ℝ)
      (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) w),
      Even (k + w) ∧ w < 12 * (m₀ : ℤ) ∧ 0 < δ ∧
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n)) ∧
      (∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n = 0) ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹) ∧
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n)) ∧
      ∀ β : SL(2, ℤ),
        (β ∉ CongruenceSubgroup.Gamma1 N ∧ -β ∉ CongruenceSubgroup.Gamma1 N) →
        (∀ j : ℤ, β * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∉ CongruenceSubgroup.Gamma1 N ∧
          -(β * ModularGroup.T ^ j * ModularGroup.S⁻¹) ∉ CongruenceSubgroup.Gamma1 N) →
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
          fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im) := by
  revert N hN k hk
  exact @_root_.P2MW.S_ModularCurve_exists_gamma1_peaked_auxiliary_form.solution
