/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt (git blob 199ec38ad558e222215d6d62e1b9724a8e686e94, sha256 a4b6942edd552502bc4a6b9d3f6481e5c05f1d77212c86fe1fe9b47aa20d0596).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpReductionModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpFrobeniusModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.reductionQExpModL_gammaH_smul_of_isFrobeniusAt (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (z : ModularCurve.JH M H) :
    ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) (σ • z) =
      ModularCurve.qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A)
        (CohCarrier.GammaH M H) ℓ
        (ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) z) := by
  revert M H ℓ hℓM A hA h σ hσ z
  exact @_root_.P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt.solution
