/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_M4aTorus_completedRayL_fe (git blob 5706d089373d3d23aa096f0f8c1babaff485ba0c, sha256 3347c29df9a85cc5a5b098c1fdb85a2a005cf1bac9ad5aa259e5d886fc411e6e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_CompletedRayL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_RayCharacterData
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_M4aTorus_completedRayL_fe

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
noncomputable section
open NumberField NumberField.InfinitePlace Complex Deep.NTSupply nonZeroDivisors
theorem M4aTorus.completedRayL_fe
    (K : Type) [Field K] [NumberField K]
    (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
    ∃ F G : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∧
      DifferentiableOn ℂ G {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∧
      (∀ s : ℂ, 1 < s.re → F s = completedRayL K 𝔣 χ S s) ∧
      (∀ s : ℂ, 1 < s.re →
        G s = completedRayL K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S s) ∧
      (∀ h𝔣 : 𝔣 ≠ ⊥, ∀ h𝔣' : 𝔣 ≠ ⊤, ∀ y₀ : K, M4aP2.IsGaussDatum K 𝔣 χ y₀ →
        M4aP2.IsPrimitiveMod K 𝔣 χ →
        ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
          F (1 - s) = (-Complex.I) ^ S.card *
            (M4aP2.gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣) : ℂ)) * G s) ∧
      (χ ≠ 1 → Differentiable ℂ F ∧ Differentiable ℂ G) := by
  revert K 𝔣 χ S hpar
  exact @_root_.P2MW.S_M4aTorus_completedRayL_fe.solution
