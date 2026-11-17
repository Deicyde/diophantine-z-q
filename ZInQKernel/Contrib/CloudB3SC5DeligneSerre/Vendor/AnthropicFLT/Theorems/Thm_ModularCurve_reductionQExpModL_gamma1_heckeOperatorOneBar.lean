/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar (git blob 662cd611ab7eedccb739cbfbdcf74b215cd63115, sha256 e0696cdfc5e2e11aea9c11461133675bf88e75f53daff3ad128a1944ea22afdf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpReductionModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpFrobeniusModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.reductionQExpModL_gamma1_heckeOperatorOneBar (M : ℕ) [NeZero M]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (hin : ModularCurve.HeckeDiamondInputsAll M)
    (h : ModularCurve.ReductionInputsQExpModL A (CongruenceSubgroup.Gamma1 M))
    (z : ModularCurve.JOne M) :
    ModularCurve.reductionQExpModL A (CongruenceSubgroup.Gamma1 M)
        (ModularCurve.heckeOperatorOneBar M ⟨ℓ, Fact.out⟩ z) =
      ModularCurve.qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A)
          (CongruenceSubgroup.Gamma1 M) ℓ
          (ModularCurve.reductionQExpModL A (CongruenceSubgroup.Gamma1 M)
            (ModularCurve.diamondOneBar M ℓ z))
        + ModularCurve.qExpFrobeniusPullbackModL (IsLocalRing.ResidueField A)
            (CongruenceSubgroup.Gamma1 M) ℓ
            (ModularCurve.reductionQExpModL A (CongruenceSubgroup.Gamma1 M) z) := by
  revert M ℓ hℓM A hA hin h z
  exact @_root_.P2MW.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar.solution
