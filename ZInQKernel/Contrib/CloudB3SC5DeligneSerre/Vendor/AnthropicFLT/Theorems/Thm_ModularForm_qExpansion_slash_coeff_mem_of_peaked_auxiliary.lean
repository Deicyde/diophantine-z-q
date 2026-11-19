/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary (git blob e4b987f4558ead64d3fda611a8fa00f1666b99f8, sha256 d622b3505b3a618ce3569d0ba945851567f4b9bcbfac5c70cf2938446062d9bb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (h : ℕ) (hh : 0 < h)
    (hT : ModularGroup.T ^ h ∈ Γ) (hS : ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ ∈ Γ)
    (R : Subring ℂ) {k w : ℤ} (hkw : Even (k + w))
    (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hG : ∀ n : ℕ, (UpperHalfPlane.qExpansion (h : ℝ) (⇑G : UpperHalfPlane → ℂ)).coeff n ∈ R)
    (Θ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) w)
    (hΘ : ∀ n : ℕ, (UpperHalfPlane.qExpansion (h : ℝ) (⇑Θ : UpperHalfPlane → ℂ)).coeff n ∈ R)
    (m₀ : ℕ) (hm₀ : w < 12 * (m₀ : ℤ))
    (hΘS₀ : ∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n = 0)
    (hΘS₁ : ∃ v ∈ R, v * (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff m₀ = 1)
    (hΘS : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ R)
    (δ : ℝ) (hδ : 0 < δ)
    (hdecay : ∀ β : SL(2, ℤ),
      (∀ j : ℤ, β * ModularGroup.T ^ j ∉ Γ ∧ -(β * ModularGroup.T ^ j) ∉ Γ) →
      (β * ModularGroup.S⁻¹ ∉ Γ ∧ -(β * ModularGroup.S⁻¹) ∉ Γ) →
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
        fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im))
    (n : ℕ) :
    (UpperHalfPlane.qExpansion 1
      ((⇑G : UpperHalfPlane → ℂ) ∣[k] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ R := by
  revert Γ h hh hT hS R k w hkw G hG Θ hΘ m₀ hm₀ hΘS₀ hΘS₁ hΘS δ hδ hdecay n
  exact @_root_.P2MW.S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary.solution
