/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_exists_residue_cuspForm_div_sub (git blob 0769aa852d9ea6349e7b12ba89cc3e3e7354a220, sha256 866532e9eaa0010c9f9aaa2437f03728b65ff950b133c12bb36c31207a3ab67f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_exists_residue_cuspForm_div_sub

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem UpperHalfPlane.exists_residue_cuspForm_div_sub
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (f : CuspForm Γ 2) (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) (t : ℂ)
    (hsimple : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≤ 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ c : ℍ → ℂ,
      (∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ),
          f (ofComplex z) / (F (ofComplex z) - t) = c τ / (z - τ) + g z) ∧
      (∀ γ ∈ Γ, ∀ τ : ℍ, c (γ • τ) = c τ) ∧
      (∀ τ : ℍ, c τ ≠ 0 →
        0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ)) ∧
      ∀ S : Finset ℍ, (∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ ∈ Γ, γ • σ = τ) →
        (∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ ∈ Γ, γ • σ = σ' → σ = σ') →
        ∑ σ ∈ S, c σ / Nat.card (MulAction.stabilizer Γ σ) = 0 := by
  revert Γ f F hF hΓ t hsimple hcusp
  exact @_root_.P2MW.S_UpperHalfPlane_exists_residue_cuspForm_div_sub.solution
