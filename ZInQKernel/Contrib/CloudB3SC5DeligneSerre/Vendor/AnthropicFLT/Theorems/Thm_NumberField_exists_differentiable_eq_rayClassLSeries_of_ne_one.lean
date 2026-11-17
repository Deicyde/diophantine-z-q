/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one (git blob 08b8f667240cc1e9303f0b4663753a5b3ace4046, sha256 54d0dda02818c9331a3ce68a0c92de07816b75bb7a299e0a6c28700a1934a4c4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_CompletedRayL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_RayCharacterData
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace Deep.NTSupply

theorem NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one
    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (hχ : χ ≠ 1)
    (S : Finset {w : InfinitePlace K // w.IsReal}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s : ℂ, 1 < s.re → g s = M4aTorus.rayClassLSeries K 𝔣 χ s := by
  revert K 𝔣 h𝔣 χ hχ S hpar
  exact @_root_.P2MW.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.solution
