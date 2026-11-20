/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul (git blob 8a3404be6b6414d1928c948d4e218ed146af8164, sha256 ab362df1512c6776e6ab4839a798b3e3792eba3ab93fa50b327e8d0e4e42522b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BorelSubgroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHeight
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHeight AutomorphicForm
open scoped NNReal

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ),
    (∀ b : Matrix.GeneralLinearGroup (Fin 2) F, b ∈ borelSubgroup F →
      ∀ g : AdelicGL2 (𝓞 F) F, φ (globalPoints (𝓞 F) F b * g) = φ g) ∧
    (∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), φ (unipotentGL2 u * g) = φ g) := by
  intro α hα μ ν hμF hνF s φ hφ

  have hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α := by
    intro u
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    haveI : BorelSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
    have h := NumberField.AdeleRing.distribHaarChar_algebraMap F u
    have key : (Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F)) : F →* AdeleRing (𝓞 F) F)) u =
        Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom u := by ext; rfl
    ext
    simp only [α, MonoidHom.coe_toHomUnits, MonoidHom.coe_comp, Function.comp_apply, Units.val_one]
    rw [key, h]
    simp
  have h1 : IsIdeleClassChar (𝓞 F) F (etaFst μ α hα s) := etaFst_isIdeleClassChar hμF hprin s
  have h2 : IsIdeleClassChar (𝓞 F) F (etaSnd ν α hα s) := etaSnd_isIdeleClassChar hνF hprin s
  refine ⟨?_, ?_⟩
  · intro b hb g
    have hmem : globalPoints (𝓞 F) F b ∈ adelicBorel (𝓞 F) F := globalPoints_mem_adelicBorel (𝓞 F) F hb
    rw [hφ _ hmem g, borelDiagFst_globalPoints (𝓞 F) F hb hmem, borelDiagSnd_globalPoints (𝓞 F) F hb hmem,
      h1, h2]
    simp
  · intro u g
    exact isInducedSection_unipotent_mul hφ u g
