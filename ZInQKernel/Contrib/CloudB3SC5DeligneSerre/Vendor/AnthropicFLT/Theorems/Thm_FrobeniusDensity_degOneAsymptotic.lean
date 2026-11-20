/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_degOneAsymptotic (git blob 266a53d8809b7f33a74f09a6e0188c0acf8ab62f, sha256 4b97f8c882da5c5ccd58127a88d0708a6e3505887e929f41d3a0369bd4787457).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_degOneAsymptotic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open NumberField
theorem FrobeniusDensity.degOneAsymptotic (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.DegOneAsymptotic L := by
  revert L
  exact @_root_.P2MW.S_FrobeniusDensity_degOneAsymptotic.solution
