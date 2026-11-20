/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_continuous_iwasawa_weyl_unipotent (git blob 4798291b85eb83c6c49a6c02663ea1396522e943, sha256 4985f1a09ed31574cf3e156060707ee8f2d93b1bfe58042254e68dd0cf1bcd21).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHeight
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_continuous_iwasawa_weyl_unipotent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHeight IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

theorem AutomorphicForm.exists_continuous_iwasawa_weyl_unipotent
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)),
    ∃ κ : AdeleRing (𝓞 F) F → AdelicGL2 (𝓞 F) F,
      Continuous κ ∧
      (∀ x, glFin (𝓞 F) F (κ x) ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F (κ x)))) ∧
      (∀ x, (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (κ x)⁻¹ ∈ adelicBorel (𝓞 F) F) ∧
      (∀ x y : AdeleRing (𝓞 F) F, ∀ v : HeightOneSpectrum (𝓞 F), x.2 v = y.2 v →
        finComponent (𝓞 F) F v (glFin (𝓞 F) F (κ x)) = finComponent (𝓞 F) F v (glFin (𝓞 F) F (κ y))) ∧
      (∀ x y : AdeleRing (𝓞 F) F, x.1 = y.1 → glArch (𝓞 F) F (κ x) = glArch (𝓞 F) F (κ y)) ∧
      (∀ (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ),
        IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ →
        ∀ x : AdeleRing (𝓞 F) F,
          φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) =
            ((adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) : ℝ) : ℂ) ^ (s + 1 / 2) * φ (κ x)) := by
  revert F
  exact @_root_.P2MW.S_AutomorphicForm_exists_continuous_iwasawa_weyl_unipotent.solution
