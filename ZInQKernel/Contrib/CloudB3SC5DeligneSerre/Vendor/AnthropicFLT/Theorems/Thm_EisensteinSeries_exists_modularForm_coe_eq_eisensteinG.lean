/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG (git blob 9eb2ea8fcf236831cf2cf8a1e6a19265b8c4d23c, sha256 37ced3762b4be309a6d085fd0289f4ddb49ddfc5606071451896c018a9e9efb0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EisensteinSeries_EisensteinG
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Matrix
open scoped MatrixGroups CongruenceSubgroup ModularForm

theorem EisensteinSeries.exists_modularForm_coe_eq_eisensteinG
    (N : ℕ) [NeZero N] (k : ℤ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    (∃ F : ModularForm Γ(N) k, ⇑F = EisensteinSeries.eisensteinG N k a) ∧
      ∀ γ : SL(2, ℤ), EisensteinSeries.eisensteinG N k a ∣[k] γ =
        EisensteinSeries.eisensteinG N k (a ᵥ* γ) := by
  revert N k hk a
  exact @_root_.P2MW.S_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG.solution
