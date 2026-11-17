/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_stableU (git blob eab0d3aa5c1398d7108ecc77f9a7e14de6f94764, sha256 9b68551f71f885d518a540f3af9e0c3340f728f3b0fea2e59a3167cd4ffe7b25).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_stableU

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
open _root_.ModularForm hiding mdifferentiable_heckeU heckeU_slash_eq_self_of_mem_GammaH

theorem CuspForm.stableU (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ}
    (hq : q.Prime) (hqM : q ∣ M) :
    CuspForm.StableU M H k q := by
  revert M H k q hq hqM
  exact @_root_.P2MW.S_CuspForm_stableU.solution
