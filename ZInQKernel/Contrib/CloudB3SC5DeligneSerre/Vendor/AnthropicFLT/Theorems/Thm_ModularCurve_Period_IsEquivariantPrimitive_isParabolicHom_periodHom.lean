/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_Period_IsEquivariantPrimitive_isParabolicHom_periodHom (git blob dbd6e2c05a94a2e25b46fd70f7df07b559e9b071, sha256 60ff88ab86f33719bd882a6a1f78443d646ca57e7e2cde4ae080c1573a0a242b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMapBundled
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_Period_IsEquivariantPrimitive_isParabolicHom_periodHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups
theorem ModularCurve.Period.IsEquivariantPrimitive.isParabolicHom_periodHom {Γ : Subgroup SL(2, ℤ)}
    {F : UpperHalfPlane → ℂ} (hF : ModularCurve.Period.IsEquivariantPrimitive Γ F)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ,
      Filter.Tendsto (fun w : UpperHalfPlane => F (δ • w)) UpperHalfPlane.atImInfty (nhds L)) :
    ModularCurve.Period.IsParabolicHom Γ hF.periodHom := by
  revert Γ F hF hlim
  exact @_root_.P2MW.S_ModularCurve_Period_IsEquivariantPrimitive_isParabolicHom_periodHom.solution
