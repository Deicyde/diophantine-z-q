/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one (git blob 53f08d65a6f8dfe9efe6215f610cc611e7ef7235, sha256 0603c61348d6e40c8f5fbcbd4d0ed1f2eaac2c4da6a42e5a603d613da6dffee7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one
    (F : Type) [Field F] [NumberField F]
    (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (hκ : κ ≠ 1) :
    ∃ (n : ℕ) (ρ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* Matrix (Fin n) (Fin n) ℂ),
      Continuous ρ ∧ ρ κ ≠ 1 := by
  revert F κ hκ
  exact @_root_.P2MW.S_AutomorphicForm_exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one.solution
