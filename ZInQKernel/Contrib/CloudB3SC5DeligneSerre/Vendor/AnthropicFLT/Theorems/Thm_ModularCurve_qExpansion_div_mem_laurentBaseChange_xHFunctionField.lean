/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField (git blob 6ac8b6764aa4caeac25f63c33e8e93be25b68a64, sha256 64f4b4ba27ed885f44ede18cd68294093618b134f7296476f26e5b6f34bf7d52).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.qExpansion_div_mem_laurentBaseChange_xHFunctionField (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) {k : ℤ}
    (f g : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k) (hg : g ≠ 0) :
    HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ∈
      ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField N H) := by
  revert N H k f g hg
  exact @_root_.P2MW.S_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField.solution
