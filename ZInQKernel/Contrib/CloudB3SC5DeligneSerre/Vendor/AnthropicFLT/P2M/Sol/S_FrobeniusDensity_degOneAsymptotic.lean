/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_FrobeniusDensity_degOneAsymptotic (git blob ed9529c6ca54e3f5b2fa5daa8ed1a9d14d2b2c3e, sha256 3ce62146ef36339f4c8e89c203817d20c5bb6313a87931ee42687b52e4a87ee2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_FrobeniusDensity_degOneSum_add_log_isBigO
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_FrobeniusDensity_summable_degOne_term
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FrobeniusDensity_DegOneAsymptotic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_FrobeniusDensity_degOneAsymptotic

set_option autoImplicit false

open NumberField

theorem solution (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.DegOneAsymptotic L := fun H S₀ =>
  ⟨fun _ hs => FrobeniusDensity.summable_degOne_term
      (FixedPoints.intermediateField H : IntermediateField ℚ L) S₀ hs,
    FrobeniusDensity.degOneSum_add_log_isBigO
      (FixedPoints.intermediateField H : IntermediateField ℚ L) S₀⟩
