/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight (git blob 95e55d38546029b0d5f9fd4b74b429201cca2c94, sha256 5c00b88c2479248512c2efd61a092ce34a8207ec2d2b685b3dcd60d06fe1e275).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHeight
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicHeight_continuous_adelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField NumberField.AdelicHeight AutomorphicForm

theorem NumberField.AdelicHeight.continuous_adelicHeight
    (F : Type) [Field F] [NumberField F] : Continuous (adelicHeight F) := by
  revert F
  exact @_root_.P2MW.S_NumberField_AdelicHeight_continuous_adelicHeight.solution
