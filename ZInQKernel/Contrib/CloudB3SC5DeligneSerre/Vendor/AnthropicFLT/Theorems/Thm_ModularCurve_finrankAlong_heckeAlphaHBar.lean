/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaHBar (git blob 660da630823c10ae6200c9868bf1c6f25c14a03f, sha256 84ff5d3164a76483c4d4f479f9014c188cb1435da40699c6511f3d9da9986ad5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHHeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_finrankAlong_heckeAlphaHBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.finrankAlong_heckeAlphaHBar (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ)
    [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeAlphaHBar L M H ℓ) = ℓ + 1 := by
  revert L M H ℓ hℓM
  exact @_root_.P2MW.S_ModularCurve_finrankAlong_heckeAlphaHBar.solution
