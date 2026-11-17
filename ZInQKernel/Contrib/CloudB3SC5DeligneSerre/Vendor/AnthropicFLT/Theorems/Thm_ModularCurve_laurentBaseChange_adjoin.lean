/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_laurentBaseChange_adjoin (git blob 1eb3cb6d1b39fb9ad8c7595eb22a708e8062f105, sha256 8a5532ae731f0da6e71c09d363c632353abb94262b47e872adef25dbd6efe955).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_laurentBaseChange_adjoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.laurentBaseChange_adjoin (L : Type*) [Field L] [Algebra ℚ L] (S : Set (LaurentSeries ℚ)) : ModularCurve.laurentBaseChange L (IntermediateField.adjoin ℚ S) = IntermediateField.adjoin L (ModularCurve.coeffEmb L '' S) := by
  revert L S
  exact @_root_.P2MW.S_ModularCurve_laurentBaseChange_adjoin.solution
