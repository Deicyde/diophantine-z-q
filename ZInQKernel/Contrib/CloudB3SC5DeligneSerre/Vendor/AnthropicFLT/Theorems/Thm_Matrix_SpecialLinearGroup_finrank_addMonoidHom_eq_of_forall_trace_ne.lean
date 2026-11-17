/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Matrix_SpecialLinearGroup_finrank_addMonoidHom_eq_of_forall_trace_ne (git blob 350cb9c11f951e4578e024356a0a7e315624ca29, sha256 3f60bf4adc44e2e35d892bb76094741452a90398a39408ca7e4e586ed91dbf54).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_eq_of_forall_trace_ne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
theorem Matrix.SpecialLinearGroup.finrank_addMonoidHom_eq_of_forall_trace_ne
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1)
    (K : Type) [Field K] [CharZero K] :
    Module.finrank K (Additive Γ →+ K) = 1 + Γ.index / 6 := by
  revert Γ hneg hΓ K
  exact @_root_.P2MW.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_eq_of_forall_trace_ne.solution
