/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_continuous_unipotentGL2 (git blob 432196200fdb47f7abf8ac79d830c261b21c6857, sha256 f88f5a7b1f2da6ed3c880ef883fd8d41f839c9dc0ce3ff9ca3eb33d59d8102d7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_continuous_unipotentGL2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AutomorphicForm.continuous_unipotentGL2 {R : Type*} [CommRing R] [TopologicalSpace R]
    [ContinuousNeg R] : Continuous fun x : R => AutomorphicForm.unipotentGL2 x := by
  revert R
  exact @_root_.P2MW.S_AutomorphicForm_continuous_unipotentGL2.solution
