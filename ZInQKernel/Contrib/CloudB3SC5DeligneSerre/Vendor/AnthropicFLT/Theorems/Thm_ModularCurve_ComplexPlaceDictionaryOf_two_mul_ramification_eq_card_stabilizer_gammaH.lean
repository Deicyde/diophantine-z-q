/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer_gammaH (git blob 77ae29e50665ac458a57903b31becda4d58f1c91, sha256 cf8eb60c8d908c1127eac130ee213bca08fb3b1fd5be82f7a856a2a28fca66a2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (τ : UpperHalfPlane) :
    2 * D.ramification τ =
      Nat.card (MulAction.stabilizer
        (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) := by
  revert M H D τ
  exact @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer_gammaH.solution
