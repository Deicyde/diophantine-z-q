/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU (git blob a184e71e85af6bea00374a9df643849d45f353b9, sha256 5ff601bbf529de4dea2e0671123b0157638728d41810fae1f29656e26468f5a1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : ⇑g = ModularForm.heckeU 2 q ⇑f) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ModularCurve.periodMapOf (CohCarrier.GammaH M H) g =
      CohCarrier.heckeT M H q ℂ (ModularCurve.periodMapOf (CohCarrier.GammaH M H) f) := by
  revert M H q hq hqM f g hg
  exact @_root_.P2MW.S_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU.solution
