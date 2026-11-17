/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff (git blob 671b26d06ce9d5434dae99a9bf1224d0126ce575, sha256 6e1a0b7605e303b79c5c9f95feaf054e9ab74b9ea8315bc92a003afe96e859fd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHDiamondModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve
open scoped MatrixGroups

universe u in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
          qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)),
      IsDiamondPullbackModL K M ⊥ ρ ∧
      ∀ (H : Subgroup (ZMod M)ˣ) (y : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)),
        (y : LaurentSeries K) ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) ↔
          ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ y = y := by
  revert K M hM
  exact @_root_.P2MW.S_ModularCurve_exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff.solution
