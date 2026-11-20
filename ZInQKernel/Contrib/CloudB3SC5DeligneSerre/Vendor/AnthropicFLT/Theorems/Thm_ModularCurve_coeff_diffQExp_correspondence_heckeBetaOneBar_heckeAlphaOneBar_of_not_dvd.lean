/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd (git blob 09cd514917efb695e0a548d9a7f0f732f95a500e, sha256 12e3cb8b9b64e14bfd90ff0b8bc934a9d587e8cbf0bfd956ac818e54db3e7ed6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1Diamond
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_HeckeDifferential
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd
    (M : ℕ) [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (hβ : ModularCurve.HeckeBetaOneDefined M ℓ)
    (hσ : ∃ σ : ↥(ModularCurve.x1FunctionField M) ≃ₐ[ℚ] ↥(ModularCurve.x1FunctionField M),
      ModularCurve.IsDiamondAut M ℓ σ)
    (hσ' : ∃ σ' : ↥(ModularCurve.x1FunctionFieldBar M) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.x1FunctionFieldBar M),
      ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ) (ModularCurve.diamondAut M ℓ) σ')
    (ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ]) (n : ℤ) :
    (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)
        (AlgebraicCurve.Differential.correspondence
          (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ)
          (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) ω)).coeff n =
      (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M) ω).coeff (n * ℓ) +
        (ℓ : AlgebraicClosure ℚ) *
          (if (ℓ : ℤ) ∣ n then
            (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)
              (AlgebraicCurve.Differential.correspondence
                (ModularCurve.diamondAutBar M ℓ).toAlgHom
                (AlgHom.id (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)) ω)).coeff
              (n / ℓ)
           else 0) := by
  revert M ℓ hℓM hβ hσ hσ' ω n
  exact @_root_.P2MW.S_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd.solution
