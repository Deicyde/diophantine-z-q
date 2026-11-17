/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_degOneSum_add_log_isBigO (git blob c35f346ba923755d7eb3f33e773de8de926d30bb, sha256 49f723aeac0f0fdc7a4fb7cb46167ec757f1ba42f1f361d9c6930d354855c346).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FrobeniusDensity_PrimeSums
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_degOneSum_add_log_isBigO

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Filter Topology Asymptotics
theorem FrobeniusDensity.degOneSum_add_log_isBigO
    (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) :
    (fun s : ℝ => (∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else
        (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
      + Real.log (s - 1)) =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1 : ℝ)) := by
  revert K S₀
  exact @_root_.P2MW.S_FrobeniusDensity_degOneSum_add_log_isBigO.solution
