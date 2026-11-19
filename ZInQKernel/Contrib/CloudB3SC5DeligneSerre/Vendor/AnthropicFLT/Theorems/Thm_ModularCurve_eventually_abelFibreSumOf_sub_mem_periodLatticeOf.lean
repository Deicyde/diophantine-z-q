/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf (git blob 0316ec8c54d721880c8fc2b9cd554c2d467c7099, sha256 46009f700f489b8baa136105318c41672f354c4ab01550d1c10c436d0327d968).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_AbelFibreSumOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hnc : ∀ (t : ℂ) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤)
    (t₀ : ℂ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t₀ ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∀ᶠ t in 𝓝 t₀,
      ModularCurve.abelFibreSumOf Γ F t - ModularCurve.abelFibreSumOf Γ F t₀ ∈
        ModularCurve.periodLatticeOf Γ := by
  revert Γ F hF hΓ hnc t₀ hcusp
  exact @_root_.P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.solution
