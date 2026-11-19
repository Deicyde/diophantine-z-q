/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn (git blob 02ccc2f7bd66519e67eecce7956a4e1447b628d4, sha256 fc6b97bba4d0ed35e257faf25f4910f1a0322478f66ec387e98ea4231ae47ee5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField

theorem AutomorphicForm.isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hf : IsFactorizableTestFn K f)
    (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    IsFactorizableTestFn K (fun y => f (t⁻¹ * y)) := by
  revert K f hf t
  exact @_root_.P2MW.S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn.solution
