/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum (git blob 354a23af855edff73881feee46acc7c01744b323, sha256 c5ebc31209aeca7a5567348498cda459376e11540c017887a6acbc82b87a0633).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPins
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain AutomorphicForm
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
set_option autoImplicit false

theorem EisensteinGeneral.Glue.whittakerCoefficient_bruhatSeries_eq_finset_sum (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1) (n : ℕ) (c : Fin n → ℂ)
    (Ψ : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΨ : ∀ i, ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ (Ψ i))
    (hΦ : ∀ g', Φ g' = ∑ i : Fin n, c i * Ψ i g') (ξ : F) (g : AdelicGL2 (𝓞 F) F)
    (hint : ∀ i, Integrable (fun y => Ψ i (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    whittakerCoefficient F (productionPins F) ψ
        (fun g' => Φ g' + ∑' ξ' : F, Φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g'))
        ξ g
      = ∑ i : Fin n, c i * whittakerCoefficient F (productionPins F) ψ
          (fun g' => Ψ i g' + ∑' ξ' : F,
            Ψ i (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) ξ g := by
  revert F ψ hψc hψ n c Ψ Φ hΨ hΦ ξ g hint
  exact @_root_.P2MW.S_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum.solution
