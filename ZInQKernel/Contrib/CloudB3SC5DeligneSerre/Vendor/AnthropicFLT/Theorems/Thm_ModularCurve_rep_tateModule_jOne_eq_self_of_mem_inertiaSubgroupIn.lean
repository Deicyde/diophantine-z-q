/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn (git blob b011be3d10f2fa4903fbf71b48a397f34a4b7b7b, sha256 06d227086049d31ae0569cbefe7fc819d31ddf0dd182a36b0b2ae08ebc8e5a91).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_TateModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn (M p : ℕ) [NeZero M]
    [Fact p.Prime]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓMp : ¬ ℓ ∣ M * p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : TateModule p (ModularCurve.JOne M)) :
    TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x = x := by
  revert M p ℓ hℓ hℓMp A hA σ hσ x
  exact @_root_.P2MW.S_ModularCurve_rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn.solution
