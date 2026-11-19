/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_TateGlobal_exists_isCompact_forall_eq_principal_mul_balanced_mul (git blob 49442f4f294fc46a2cb3e577fc595bbf184687c4, sha256 0a6c5f09986cd89fe93917cfe3c2c52e9681f6124f3c17cc7acd68f4acd387ac).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_TateGlobal_exists_isCompact_forall_eq_principal_mul_balanced_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped NNReal

theorem NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∃ U : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact U ∧ (∀ u ∈ U, ((α u : ℝˣ) : ℝ) = 1) ∧
      ∀ y : (AdeleRing (𝓞 F) F)ˣ, ∃ (η : Fˣ) (z u : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ),
        u ∈ U ∧ 0 < r ∧
        y = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * z * u ∧
        (z : AdeleRing (𝓞 F) F).2 = 1 ∧
        (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) ∧
        ((α z : ℝˣ) : ℝ) = r ^ Module.finrank ℚ F := by
  revert F
  exact @_root_.P2MW.S_NumberField_TateGlobal_exists_isCompact_forall_eq_principal_mul_balanced_mul.solution
