/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite (git blob 163b2090feb5dffdad3ab1786d00194adcb76b52, sha256 e19438e7c83a541f08e8c012e0315ba76ecca18f9ef6674182b559c922f645c8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ResidualRealization
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.exists_semisimple_descent_of_trace_det_mem_range_finite
    {K L : Type} [Field K] [Field L] [Algebra K L] (M p : ℕ) [Fact p.Prime]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (k : Type) [Field k] [Finite k] (ι : k →+* Ω)
    (V : Type) [AddCommGroup V] [Module Ω V] (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[Ω] V))
    (hp : (p : Ω) = 0) (hV : Module.finrank Ω V = 2) (hfin : Finite ρ.range)
    (hirr : ∀ W : Submodule Ω V, (∀ σ, ∀ v ∈ W, ρ σ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ σ, LinearMap.trace Ω V (ρ σ).toLinearMap ∈ ι.range)
    (hdet : ∀ σ, LinearMap.det (ρ σ).toLinearMap ∈ ι.range)
    (hcyc : ModularCurve.CyclotomicDeterminant M p ρ) :
    ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module k V₀)
      (ρ₀ : (L ≃ₐ[K] L) →* (V₀ ≃ₗ[k] V₀)),
      Module.finrank k V₀ = 2 ∧
      ModularCurve.CyclotomicDeterminant M p ρ₀ ∧
      ρ.ker ≤ ρ₀.ker ∧
      (∀ σ, ι (LinearMap.trace k V₀ (ρ₀ σ).toLinearMap) = LinearMap.trace Ω V (ρ σ).toLinearMap) ∧
      (∀ σ, ι (LinearMap.det (ρ₀ σ).toLinearMap) = LinearMap.det (ρ σ).toLinearMap) ∧
      (∀ W : Submodule k V₀, (∀ σ, ∀ v ∈ W, ρ₀ σ v ∈ W) →
        ∃ W' : Submodule k V₀, (∀ σ, ∀ v ∈ W', ρ₀ σ v ∈ W') ∧ IsCompl W W') := by
  revert K L M p Ω k ι V ρ hp hV hfin hirr htr hdet hcyc
  exact @_root_.P2MW.S_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite.solution
