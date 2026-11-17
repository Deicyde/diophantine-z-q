/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_IsKfSmooth_exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq (git blob 5ed6eeaa5a5a77c59812d6ba772659f6fdc24e69, sha256 354688b3420a7432e9ed29477f74622cd2326382149f5d0eed5cae28cfcd37cf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_IsKfSmooth_exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq
    (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsKfSmooth F φ) :
    ∃ (U : Subgroup (AdelicGL2 (𝓞 F) F)) (_ : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
      (O : Subgroup (AdelicGL2 (𝓞 F) F)) (_ : IsOpen (O : Set (AdelicGL2 (𝓞 F) F))),
      U = O ⊓ finiteAdelicGL2Subgroup F ∧ ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g := by
  revert F φ hφ
  exact @_root_.P2MW.S_AutomorphicForm_IsKfSmooth_exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq.solution
