/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd (git blob 09be641bb4d358a6eed4603f8f9b64172392e847, sha256 77d22a856dfe76a47af3600a98f4d2c11e28ae4e6f9127039cd5ea2f5812a269).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpReductionModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_reductionInputsQExpModL_of_finrank_le_of_genusFF_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_genusFF_gammaH_residueField_eq_of_not_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd

set_option autoImplicit false

open ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (M : ℕ)
    [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    (∃ x : ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H,
        Transcendental (IsLocalRing.ResidueField A) x ∧
          FiniteDimensional
            (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              ({x} : Set (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)))
            (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)) ∧
      ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H) := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  obtain ⟨x, -, htr, hfin, -⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
      (AlgebraicClosure ℚ) A (CohCarrier.GammaH M H) hT
  refine ⟨⟨x, htr, hfin⟩, ?_⟩
  exact ModularCurve.reductionInputsQExpModL_of_finrank_le_of_genusFF_eq (CohCarrier.GammaH M H) hT A
    (fun x y hx hy =>
      ModularCurve.finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd M H hℓM A hA x y hx hy)
    (ModularCurve.genusFF_gammaH_residueField_eq_of_not_dvd M H hℓM A hA)
