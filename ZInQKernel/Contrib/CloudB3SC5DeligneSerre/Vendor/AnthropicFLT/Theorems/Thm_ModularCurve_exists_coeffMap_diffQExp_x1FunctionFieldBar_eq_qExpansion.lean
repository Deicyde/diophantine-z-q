/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion (git blob b51809eb646160f1f1d0abf1196bd6c4f50fc01d, sha256 71ab922b003637f22541ee964145c0ffe1cdb85166044e9620f489d54bcde7d6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_HeckeDifferential
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped TensorProduct

theorem ModularCurve.exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion
    (M : ℕ) [NeZero M] (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (hf : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 ⇑f).coeff n ∈ ι₀.range) :
    ∃ ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ],
      ModularCurve.coeffMap ι₀ (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M) ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) := by
  revert M ι₀ f hf
  exact @_root_.P2MW.S_ModularCurve_exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion.solution
