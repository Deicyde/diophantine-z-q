/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_heckeOperatorHAlong_diamondHBar_comm (git blob d2a6dea4fb608a159a2e85a04705c473e0bf80c5, sha256 1cc1b33816b3f29baadde026e08bb4642bea7d22b6c5a1f06b0cc0d9c4ab9995).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_heckeOperatorHAlong_diamondHBar_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.heckeOperatorHAlong_diamondHBar_comm (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime] (d : (ZMod M)ˣ) (P : ModularCurve.JH M H) :
    ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ (ModularCurve.diamondHBar M H d P) =
      ModularCurve.diamondHBar M H d
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ P) := by
  revert M H ℓ d P
  exact @_root_.P2MW.S_ModularCurve_heckeOperatorHAlong_diamondHBar_comm.solution
