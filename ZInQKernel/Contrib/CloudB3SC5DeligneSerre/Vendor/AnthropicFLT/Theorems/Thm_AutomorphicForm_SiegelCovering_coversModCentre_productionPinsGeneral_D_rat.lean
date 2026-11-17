/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat (git blob 566ef2a76cf458477d76d249cd15ae1394718223, sha256 4de1371606c852b39d04d5f071490681a25687e20025d5be144d7af56c33002a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat :
    CoversModCentre ℚ (productionPinsGeneral ℚ).D := @_root_.P2MW.S_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat.solution
