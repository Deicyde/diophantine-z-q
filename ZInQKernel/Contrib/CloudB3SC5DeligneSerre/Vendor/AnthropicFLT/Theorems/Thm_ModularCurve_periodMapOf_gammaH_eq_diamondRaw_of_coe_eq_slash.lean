/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash (git blob a15cf1c96c338a349e982276b8a5be856c06b4c6, sha256 2a73ab21d9f5e09309ada9e11af3f7ac6dd8c05b710eebd0a6fa0803c13b6f56).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (σ : CongruenceSubgroup.Gamma0 M)
    (f g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : ⇑g = ⇑f ∣[(2 : ℤ)] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))) :
    ModularCurve.periodMapOf (CohCarrier.GammaH M H) g =
      CohCarrier.diamondRaw M H ℂ σ (ModularCurve.periodMapOf (CohCarrier.GammaH M H) f) := by
  revert M H σ f g hg
  exact @_root_.P2MW.S_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash.solution
