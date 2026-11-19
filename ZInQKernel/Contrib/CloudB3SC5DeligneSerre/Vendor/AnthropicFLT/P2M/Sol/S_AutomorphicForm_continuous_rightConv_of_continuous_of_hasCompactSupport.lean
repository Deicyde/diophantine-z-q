/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport (git blob 2b53699e7599e8320936c4f275cfa0231ad0c435, sha256 c32468f10d9dd676ca1940678a0f2dc1470bc5a9f479a6c88eeb069402928061).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    (φ : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hφ : Continuous φ)
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (AutomorphicForm.rightConv F φ g) := by
  haveI : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 F) F)) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SecondCountableTopology (GL (Fin 2) (AdeleRing (𝓞 F) F)) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  have hcont : Continuous (Function.uncurry fun (x y : GL (Fin 2) (AdeleRing (𝓞 F) F)) => φ (x * y) * g y) :=
    (hφ.comp continuous_mul).mul (hg.comp continuous_snd)
  have h := continuous_parametric_integral_of_continuous
    (μ := NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) hcont hgc.isCompact
  have heq : AutomorphicForm.rightConv F φ g =
      fun x => ∫ y in tsupport g, φ (x * y) * g y ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    funext x
    rw [AutomorphicForm.rightConv_apply]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]).symm
  rw [heq]
  exact h
