/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_summable_degOne_term (git blob 20a2416157fe0e40f4b80378bf55e7f0578397df, sha256 bb3fcf3152ae6975a6e545f6577769d4c00a2ecef6a2db573a7d6ee573d01822).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FrobeniusDensity_PrimeSums
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_summable_degOne_term

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem FrobeniusDensity.summable_degOne_term
    (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) {s : ℝ} (hs : 1 < s) :
    Summable (fun ℓ : ℕ => (if ℓ ∈ S₀ then 0 else
      (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)) := by
  revert K S₀ s hs
  exact @_root_.P2MW.S_FrobeniusDensity_summable_degOne_term.solution
