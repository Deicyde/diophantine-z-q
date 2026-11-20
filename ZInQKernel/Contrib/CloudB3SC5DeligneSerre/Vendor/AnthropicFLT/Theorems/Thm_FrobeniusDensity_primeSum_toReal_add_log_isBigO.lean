/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO (git blob 5002cc0a9e61d743e38792e0eb93cc24781f9a54, sha256 74e59e6b55f087f94438d17b1d47b7845b6783866d835d02c5eae980d79e0a67).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FrobeniusDensity_PrimeSums
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Filter Topology Asymptotics
theorem FrobeniusDensity.primeSum_toReal_add_log_isBigO
    (K : Type*) [Field K] [NumberField K] :
    (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
      =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1:ℝ)) := by
  revert K
  exact @_root_.P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.solution
