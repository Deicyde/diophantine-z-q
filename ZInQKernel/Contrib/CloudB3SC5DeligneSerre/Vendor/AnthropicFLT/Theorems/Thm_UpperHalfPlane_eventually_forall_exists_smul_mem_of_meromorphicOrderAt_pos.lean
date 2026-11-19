/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos (git blob 3838f59d3585bc44eae7b70fc6d1b0a3e4b7811b, sha256 00a36492f85d0a1e8e58ddabc210207d6c89dc6ee4c71baf4dbdeaf38117fc44).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem UpperHalfPlane.eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) (t₀ : ℂ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t₀ ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    {U : Set ℍ} (hU : IsOpen U)
    (hfib : ∀ τ : ℍ, 0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t₀) (τ : ℂ) →
      ∃ γ ∈ Γ, γ • τ ∈ U) :
    ∀ᶠ t in 𝓝 t₀, ∀ τ : ℍ,
      0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) →
        ∃ γ ∈ Γ, γ • τ ∈ U := by
  revert Γ F hF hΓ t₀ hcusp U hU hfib
  exact @_root_.P2MW.S_UpperHalfPlane_eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos.solution
