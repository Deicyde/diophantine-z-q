/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd (git blob 1e184f6a0af33e1967fb44cd1c30c55a3517de32, sha256 6178044b37d53176c521fe987f54b41adf42897cb66e303fb482af7399b97da9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpReductionModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd (M : ℕ)
    [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    (∃ x : ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H,
        Transcendental (IsLocalRing.ResidueField A) x ∧
          FiniteDimensional
            (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              ({x} : Set (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)))
            (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)) ∧
      ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H) := by
  revert M H ℓ hℓM A hA
  exact @_root_.P2MW.S_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd.solution
