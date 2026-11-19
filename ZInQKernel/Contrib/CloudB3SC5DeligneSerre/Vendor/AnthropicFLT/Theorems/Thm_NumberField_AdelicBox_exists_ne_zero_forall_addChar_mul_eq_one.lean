/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicBox_exists_ne_zero_forall_addChar_mul_eq_one (git blob 24ce599e563541c075304567bfd28e651f45ad89, sha256 b3492eb2be187516c96cb6d151a312294b25595374cf3ddbc22557cd2b47184f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicBox_exists_ne_zero_forall_addChar_mul_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors
theorem NumberField.AdelicBox.exists_ne_zero_forall_addChar_mul_eq_one
    (F : Type) [Field F] [NumberField F]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
      ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) = 1 := by
  revert F ψf hψf
  exact @_root_.P2MW.S_NumberField_AdelicBox_exists_ne_zero_forall_addChar_mul_eq_one.solution
