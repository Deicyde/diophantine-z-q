/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_stableT (git blob 3609e48ba517a62e64845307b3de4a8d7c7441ee, sha256 0aa2268452e49e2fd261d98a91413743931dd1990b328c7ca22edee1fd6f2b13).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_heckeU_add_slash_slash_eq_self_of_mem_GammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_mdifferentiable_heckeU
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspFormClass_isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_stableT

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm.StableT M H k ℓ := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  intro ρ hρ f
  refine ⟨fun γ hγ => ModularForm.heckeU_add_slash_slash_eq_self_of_mem_GammaH M H k hℓ hℓM ρ hρ
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ,
    (ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k ℓ).add ((CuspFormClass.holo f).slash k _),
    fun c hc => ?_⟩
  rw [SlashAction.slash_mul]
  exact (CuspFormClass.isZeroAt_heckeU f ℓ hc).add
    (CuspFormClass.isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0 M H k ℓ ρ f hc)
