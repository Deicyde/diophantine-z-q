/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_heckeOperatorHAlong (git blob 375c1c280e2235c8bdbd50cc758804426a7a3ba3, sha256 ef92cc73fc00b0819c83684b1e10547520b863672310149c5c797c7e967002c4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpReductionModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpFrobeniusModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_reductionQExpModL_gammaH_heckeOperatorHAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.reductionQExpModL_gammaH_heckeOperatorHAlong (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H))
    (z : ModularCurve.JH M H) :
    ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H)
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ z) =
      ModularCurve.qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A)
          (CohCarrier.GammaH M H) ℓ
          (ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H)
            (ModularCurve.diamondHBar M H
              (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)) z))
        + ModularCurve.qExpFrobeniusPullbackModL (IsLocalRing.ResidueField A)
            (CohCarrier.GammaH M H) ℓ
            (ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) z) := by
  revert M H ℓ hℓM A hA hin h z
  exact @_root_.P2MW.S_ModularCurve_reductionQExpModL_gammaH_heckeOperatorHAlong.solution
