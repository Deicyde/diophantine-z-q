/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex (git blob bc1ca3c4b4e778571b7e75510011466e36a3b685, sha256 b43e979bcd9c56681e5b6ec870ae84a72b67a3a8c8ee5c400171c0d7ceb1b078).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open UpperHalfPlane
open scoped MatrixGroups Topology

set_option autoImplicit false

theorem ModularCurve.exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ S : Finset ℍ,
      (∀ s ∈ S, ∀ t ∈ S,
        (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t) ∧
      ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ 0 →
        ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ := by
  revert Γ F k hF hχ hcusp
  exact @_root_.P2MW.S_ModularCurve_exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex.solution
