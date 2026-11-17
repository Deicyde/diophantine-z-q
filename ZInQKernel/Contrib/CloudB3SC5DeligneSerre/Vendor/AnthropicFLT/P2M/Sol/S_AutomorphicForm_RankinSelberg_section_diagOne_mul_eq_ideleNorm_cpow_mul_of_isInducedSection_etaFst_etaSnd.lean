/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_RankinSelberg_section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd (git blob 04ecc756c4e79e7010c2033720be67011fb9d555, sha256 b10c201a0a6902f0657cac3442c79a2ce2026f136afba635e9b90073b775bab8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchType
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_IdeleProductMeasure
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_RankinSelberg_section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

namespace Ws50CH1

theorem diagOne_mem_adelicBorel (K : Type) [Field K] [NumberField K] (t : (AdeleRing (𝓞 K) K)ˣ) :
    diagOne t ∈ adelicBorel (𝓞 K) K := by
  show ((diagOne t : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0
  rw [diagOne_coe_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

theorem borelDiagFst_diagOne (K : Type) [Field K] [NumberField K] (t : (AdeleRing (𝓞 K) K)ˣ)
    (hmem : diagOne t ∈ adelicBorel (𝓞 K) K) :
    borelDiagFst (⟨diagOne t, hmem⟩ : ↥(adelicBorel (𝓞 K) K)) = t := by
  apply Units.ext
  show ((diagOne t : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = (t : AdeleRing (𝓞 K) K)
  rw [diagOne_coe_apply, Matrix.diagonal_apply_eq]
  rfl

theorem borelDiagSnd_diagOne (K : Type) [Field K] [NumberField K] (t : (AdeleRing (𝓞 K) K)ˣ)
    (hmem : diagOne t ∈ adelicBorel (𝓞 K) K) :
    borelDiagSnd (⟨diagOne t, hmem⟩ : ↥(adelicBorel (𝓞 K) K)) = 1 := by
  apply Units.ext
  show ((diagOne t : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 =
    ((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
  rw [diagOne_coe_apply, Matrix.diagonal_apply_eq, Units.val_one]
  rfl

end Ws50CH1

theorem solution (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s)),
    ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K), k ∈ adelicMaximalCompact K → ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        φ s (diagOne t * k) = ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * φ s k := by
  intro α hα φ hφ s k _ t
  have hαt : (((α t : ℝˣ) : ℝ) : ℂ) = ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) := rfl
  rw [hφ s (diagOne t) (Ws50CH1.diagOne_mem_adelicBorel K t) k, Ws50CH1.borelDiagFst_diagOne, Ws50CH1.borelDiagSnd_diagOne,
    map_one, Units.val_one, mul_one, etaFst_apply, MonoidHom.one_apply, one_mul, cpowChar_apply_val, hαt]
