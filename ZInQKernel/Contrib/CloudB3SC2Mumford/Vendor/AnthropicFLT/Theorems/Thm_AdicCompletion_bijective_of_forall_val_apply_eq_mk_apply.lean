/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

theorem AdicCompletion.bijective_of_forall_val_apply_eq_mk_apply
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N]
    (θ : AdicCompletion I (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] AdicCompletion I N))
    (hθ : ∀ (x : AdicCompletion I (M →ₗ[A] N)) (n : ℕ) (g : M →ₗ[A] N),
      Submodule.Quotient.mk g = x.val n →
        ∀ m : M, (θ x m).val n = Submodule.Quotient.mk (g m)) :
    Function.Bijective θ := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply.solution
