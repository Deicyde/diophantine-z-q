/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary (git blob 85b32d51dd34107fa64e17743ec5990fd9cd99ab, sha256 2eb635d516a4fd0a787aabfe07d927fe71feb9c922f433a0bfa4924dfb17a4fe).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchKFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPins
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (s : ℂ) (_hs : 1 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφf : IsKfSmooth F φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    Summable (fun ξ : F => whittakerCoefficient F (productionPins F) ψ E ξ g) := by
  revert F
  exact @_root_.P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.solution
