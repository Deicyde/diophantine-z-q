/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_stableT (git blob 7c536fc1033ad1fce4bc1fccecaf8faf25c265bd, sha256 c30897a746b37243c2424310518049f9f75da2ccb8ee5d922dbac41e32563ead).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_stableT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace MatrixGroups
end MatrixGroups
namespace ModularForm
end ModularForm


set_option autoImplicit false

open _root_.MatrixGroups
open _root_.ModularForm hiding mdifferentiable_heckeU heckeU_add_slash_slash_eq_self_of_mem_GammaH

theorem CuspForm.stableT (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm.StableT M H k ℓ := by
  revert M H k ℓ hℓ hℓM
  exact @_root_.P2MW.S_CuspForm_stableT.solution
