/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isClosed_rationalCentreUnipotent (git blob 015b51bc8a0f07a9f1dcd6236574dd374cf84d51, sha256 e04fba60b09868057aa3dbc1da23e55e080224129369eebba4190fe239027fed).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isClosed_rationalCentreUnipotent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.isClosed_rationalCentreUnipotent (K : Type) [Field K] [NumberField K] :
    IsClosed (rationalCentreUnipotent K : Set (AdelicGL2 (𝓞 K) K)) := by
  revert K
  exact @_root_.P2MW.S_AutomorphicForm_isClosed_rationalCentreUnipotent.solution
