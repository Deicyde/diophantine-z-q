/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_tailSum_le (git blob e642ccb605c5fa0ee6c9ef5396620f4d062a809f, sha256 e5d55f055ff7744e526717c378c466a879792d9df39f57cae63273a60182794b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FrobeniusDensity_PrimeSums
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_tailSum_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField
open scoped ENNReal

theorem FrobeniusDensity.tailSum_le
    (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 ≤ s) :
    FrobeniusDensity.tailSum K s ≤ (Module.finrank ℚ K : ℝ≥0∞) * FrobeniusDensity.tailConst := by
  revert K s hs
  exact @_root_.P2MW.S_FrobeniusDensity_tailSum_le.solution
