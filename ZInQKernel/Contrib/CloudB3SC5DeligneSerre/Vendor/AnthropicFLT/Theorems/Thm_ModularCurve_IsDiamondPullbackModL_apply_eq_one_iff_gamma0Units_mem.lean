/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_IsDiamondPullbackModL_apply_eq_one_iff_gamma0Units_mem (git blob 5e2adabab9c97d4677889d4c94d087a3c75b95da, sha256 4b2a6403a326653a3fdd9fb45c1d98493b3004bee27a58573dfbde94cdbee659).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHDiamondModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_IsDiamondPullbackModL_apply_eq_one_iff_gamma0Units_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups in

theorem ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem
    {K : Type*} [Field K] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
    {ρ : CongruenceSubgroup.Gamma0 M →*
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))}
    (hρ : ModularCurve.IsDiamondPullbackModL K M H ρ) (γ : CongruenceSubgroup.Gamma0 M) :
    ρ γ = 1 ↔ CohCarrier.gamma0Units M γ ∈ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ) := by
  revert K M H ρ hρ γ
  exact @_root_.P2MW.S_ModularCurve_IsDiamondPullbackModL_apply_eq_one_iff_gamma0Units_mem.solution
