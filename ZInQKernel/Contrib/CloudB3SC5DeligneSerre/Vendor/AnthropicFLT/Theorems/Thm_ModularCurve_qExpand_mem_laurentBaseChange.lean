/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_qExpand_mem_laurentBaseChange (git blob d9c7968a83a088722d929d0a4a12e7d385279a5b, sha256 54a68461ffe32ccc3998827bd6985ac54459d82fd4631d380aeaf07c38903fc7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_qExpand_mem_laurentBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.qExpand_mem_laurentBaseChange {L : Type*} [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ) [NeZero n] {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, ModularCurve.qExpand ℚ n y ∈ F₁) {x : LaurentSeries L} (hx : x ∈ ModularCurve.laurentBaseChange L F₀) : ModularCurve.qExpand L n x ∈ ModularCurve.laurentBaseChange L F₁ := by
  revert L F₀ n F₁ hF x hx
  exact @_root_.P2MW.S_ModularCurve_qExpand_mem_laurentBaseChange.solution
