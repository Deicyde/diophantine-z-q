/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero (git blob 7196a9cb9b6b603d84a4992a40eda8e9c4ae4fbd, sha256 8fc7e353e24feb4a63c17bc51bd0ceed1cef54286196888121b33e1aba53dce0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem UpperHalfPlane.levelOne_sum_residue_div_card_stabilizer_eq_zero
    (ω : ℍ → ℂ) (c : ℍ → ℂ) (S : Finset ℍ)
    (hΓ : ∀ γ : SL(2, ℤ), ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∃ δ : ℝ, 0 < δ ∧ ω =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = c τ / (z - τ) + g z)
    (hS : ∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ : SL(2, ℤ), γ • σ = τ)
    (hinj : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ : SL(2, ℤ), γ • σ = σ' → σ = σ') :
    ∑ σ ∈ S, c σ / Nat.card (MulAction.stabilizer SL(2, ℤ) σ) = 0 := by
  revert ω c S hΓ hcusp hloc hS hinj
  exact @_root_.P2MW.S_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero.solution
