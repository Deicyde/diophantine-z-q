/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_IsInducedSection_eq_of_eqOn_maximalCompact (git blob 57a54c5ac5fbdcb460a4304e352837b801b2d269, sha256 77a2e76a87db573583653a5b3f19553bbb668021dd6d9bcac1f47236fcd8a61e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_PeterssonIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WindowedSiegelSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_IsInducedSection_eq_of_eqOn_maximalCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.IsInducedSection.eq_of_eqOn_maximalCompact
    (K : Type) [Field K] [NumberField K]
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (φ φ' : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) (hφ' : IsInducedSection (𝓞 K) K χ₁ χ₂ φ')
    (h : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
      (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) → φ k = φ' k) :
    φ = φ' := by
  revert K χ₁ χ₂ φ φ' hφ hφ' h
  exact @_root_.P2MW.S_AutomorphicForm_IsInducedSection_eq_of_eqOn_maximalCompact.solution
