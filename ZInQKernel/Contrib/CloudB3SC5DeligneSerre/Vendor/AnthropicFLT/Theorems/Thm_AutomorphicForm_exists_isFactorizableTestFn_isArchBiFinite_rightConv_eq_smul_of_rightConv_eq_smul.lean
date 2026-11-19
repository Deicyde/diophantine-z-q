/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul (git blob f8cb83602e3d1b97041e0360d0bd284b7ac5b966, sha256 51fce63ec3ec600390f434b0076fdc84e3ce8cce606c5076f33ca241a6fab5fe).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφt : φ ∈ archCutSubmodule F tys)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (lam : ℂ)
    (heig : rightConv F φ f = lam • φ) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧
      rightConv F φ f' = lam • φ := by
  revert F tys φ hφc hφt f hf lam heig
  exact @_root_.P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul.solution
