/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue (git blob ad7ee914c067513f7d30cc4a90d20c5824f3033c, sha256 0e526c9b7148710b40c3f8f6be8134257d7f86802342b716f7f5b692f0aa9dd1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.exists_meromorphic_smul_eq_mul_of_slashInvariant_residue
    (Γ : Subgroup SL(2, ℤ)) (m : ℍ → ℤ) (ω : ℍ → ℂ)
    (hΓ : ∀ γ ∈ Γ, ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
      (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hres : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = (m τ : ℂ) / (z - τ) + g z) ∧
      (m τ = 0 → ω τ = g τ)) :
    ∃ (F : ℍ → ℂ) (χ : Γ → ℂ),
      (∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) ∧
      (∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ) ∧
      (∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) ∧
      ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (m τ : WithTop ℤ) := by
  revert Γ m ω hΓ hcusp hres
  exact @_root_.P2MW.S_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue.solution
