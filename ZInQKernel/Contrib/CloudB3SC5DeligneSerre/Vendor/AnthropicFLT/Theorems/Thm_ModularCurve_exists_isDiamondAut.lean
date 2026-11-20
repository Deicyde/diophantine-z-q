/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_isDiamondAut (git blob 7674533550bcfa463828117474611c4145a0f97a, sha256 748368379231d4804a62d09745e5c504acd80037c4c97ce318211a7fc73191fa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1Diamond
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_isDiamondAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.exists_isDiamondAut (M : ℕ) [NeZero M] {d : ℕ} (hd : Nat.Coprime d M) :
    ∃ σ : ModularCurve.x1FunctionField M ≃ₐ[ℚ] ModularCurve.x1FunctionField M,
      ModularCurve.IsDiamondAut M d σ := by
  revert M d hd
  exact @_root_.P2MW.S_ModularCurve_exists_isDiamondAut.solution
