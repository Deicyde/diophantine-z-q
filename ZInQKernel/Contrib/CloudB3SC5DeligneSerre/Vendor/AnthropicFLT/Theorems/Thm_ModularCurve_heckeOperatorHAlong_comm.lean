/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_heckeOperatorHAlong_comm (git blob b1ce5891388206e0b9770f6130f3e63f11d2a816, sha256 77a190152de654edc0d3d6a555ee270363c8145d34c78ec701f76d006ba319d4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHHeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_heckeOperatorHAlong_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.heckeOperatorHAlong_comm (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ℓ ℓ' : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] (P : ModularCurve.JH M H) :
    ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ' P) =
      ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ'
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ P) := by
  revert M H ℓ ℓ' P
  exact @_root_.P2MW.S_ModularCurve_heckeOperatorHAlong_comm.solution
