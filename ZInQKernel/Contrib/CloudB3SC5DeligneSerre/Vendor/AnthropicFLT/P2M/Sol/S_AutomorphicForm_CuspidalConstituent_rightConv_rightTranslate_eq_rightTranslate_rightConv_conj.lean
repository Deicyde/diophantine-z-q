/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj (git blob 114c1ae60f09a6b6246b6403cef590829f1af5a0, sha256 eedfdd7b4a015d1875c20a6311d20bce4f7478e662b664901469f3748485cc90).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem solution
    (F : Type) [Field F] [NumberField F]
    (h : AdelicGL2 (𝓞 F) F) (φ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F (rightTranslate F h φ) f = rightTranslate F h (rightConv F φ (fun y => f (h * y * h⁻¹))) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  funext g
  show (∫ x, rightTranslate F h φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F))
      = ∫ x, φ (g * h * x) * f (h * x * h⁻¹) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
  simp only [rightTranslate_apply]

  have h1 := integral_mul_left_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    (fun x => φ (g * h * x) * f (h * x * h⁻¹)) h⁻¹
  simp only [← mul_assoc, mul_inv_cancel_right, mul_inv_cancel, one_mul] at h1

  have h2 := integral_mul_right_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    (fun x => φ (g * x) * f (x * h⁻¹)) h
  simp only [mul_inv_cancel_right, ← mul_assoc] at h2

  rw [h2, h1]
