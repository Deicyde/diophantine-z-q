/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_primeSum_eq_degOneSum_add (git blob a798be7e49724f6398716e67d36948d37c23950e, sha256 906cb26e00250ec2b1562ded5a01ecc81fbdeb1fa4f02f4ba5fe42267229bd57).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FrobeniusDensity_PrimeSums
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_primeSum_eq_degOneSum_add

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem FrobeniusDensity.primeSum_eq_degOneSum_add
    (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) (s : ℝ) :
    FrobeniusDensity.primeSum K s =
      FrobeniusDensity.degOneSum K S₀ s + FrobeniusDensity.cutSum K S₀ s +
      FrobeniusDensity.tailSum K s := by
  revert K S₀ s
  exact @_root_.P2MW.S_FrobeniusDensity_primeSum_eq_degOneSum_add.solution
