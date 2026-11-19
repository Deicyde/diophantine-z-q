/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_bot_of_natCast_ne_zero (git blob da4d375b9859fe2f59bf9b506d678a295b6096c2, sha256 74c19847a90103172a6bf9de1b4250ea6cfd29632fcb36850ef4d1bd491ae25b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHDiamondModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_isDiamondPullbackModL_bot_of_natCast_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve
open scoped MatrixGroups

universe u in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_isDiamondPullbackModL_bot_of_natCast_ne_zero
    (K : Type u) [Field K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
          qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)),
      IsDiamondPullbackModL K M ⊥ ρ := by
  revert K M hM
  exact @_root_.P2MW.S_ModularCurve_exists_isDiamondPullbackModL_bot_of_natCast_ne_zero.solution
