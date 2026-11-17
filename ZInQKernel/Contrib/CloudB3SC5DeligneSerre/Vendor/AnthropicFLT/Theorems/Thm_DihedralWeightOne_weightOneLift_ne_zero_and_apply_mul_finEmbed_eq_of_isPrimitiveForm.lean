/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DihedralWeightOne_weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm (git blob 7b3e52cc1f701e49afbcfab5a9cdd5f9f65c3990, sha256 cc1444eb7cb2f903c1bbf0e3166766bc1d036ef0a91ad3cd83acdd45626fc5c4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_ConductorDatum
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_AdelicSpanCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DihedralWeightOne_weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField AutomorphicForm DihedralWeightOne IsDedekindDomain
open CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem DihedralWeightOne.weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm
    (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf : CuspForm.IsPrimitiveForm ψ f) :
    weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f) ≠ 0 ∧
    ∀ g ∈ NumberField.AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N),
      ∀ x, weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f) (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ g) =
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f) x := by
  revert N ψ f hf
  exact @_root_.P2MW.S_DihedralWeightOne_weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm.solution
