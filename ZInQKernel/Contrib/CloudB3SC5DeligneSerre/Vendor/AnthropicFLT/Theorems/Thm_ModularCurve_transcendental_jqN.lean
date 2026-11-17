/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_transcendental_jqN (git blob bce9ab51e37289311ea265c4391be7c138f581da, sha256 65fca9c1eca2c9fa9c2110bb5416d6006fd8ea755e5e65e6459edac3e3b00e0e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_transcendental_jqN

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve IntermediateField
theorem ModularCurve.transcendental_jqN (N : ℕ) [NeZero N] : Transcendental ℚ (jqN N) := by
  revert N
  exact @_root_.P2MW.S_ModularCurve_transcendental_jqN.solution
