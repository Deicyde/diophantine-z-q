/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj (git blob e4a8ed8bdb24d9907bf31eae9c7a55cbb0e27d4b, sha256 496b9ecae12e084572b9ef37ccd50f3dc7c2d893d70376f3324315186b78f9eb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open _root_.NumberField.AdelicHaar hiding isMulRightInvariant_adelicGLHaar
open _root_.NumberField.AdelicLevel
open _root_.NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj
    (F : Type) [Field F] [NumberField F]
    (h : AdelicGL2 (𝓞 F) F) (φ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F (rightTranslate F h φ) f = rightTranslate F h (rightConv F φ (fun y => f (h * y * h⁻¹))) := by
  revert F h φ f
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj.solution
