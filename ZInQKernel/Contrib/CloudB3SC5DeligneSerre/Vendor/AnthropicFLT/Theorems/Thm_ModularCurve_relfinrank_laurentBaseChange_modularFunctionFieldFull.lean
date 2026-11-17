/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull (git blob a91bff9e0e26dc1066f44d90e88d26fdd2b26e9a, sha256 903a5014bab208f22ae9d5f45457345effaf1a682a865404c2d42b37c7943c81).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QAdicPlace
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.FieldTheory.Relrank
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve

theorem ModularCurve.relfinrank_laurentBaseChange_modularFunctionFieldFull (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] : IntermediateField.relfinrank (IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))) (laurentBaseChange L (modularFunctionFieldFull N)) = IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularFunctionFieldFull N) := by
  revert L N
  exact @_root_.P2MW.S_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull.solution
