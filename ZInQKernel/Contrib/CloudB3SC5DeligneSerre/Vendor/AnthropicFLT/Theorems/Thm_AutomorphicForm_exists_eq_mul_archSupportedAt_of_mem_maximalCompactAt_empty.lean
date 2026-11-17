/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty (git blob e694ff2e3cec47d44818f77a21ab7b06edd5f8e0, sha256 bbab4736a78d97325ae58331d522d4d5ed93cf29fc4875ce2df3ab64ef7cf2af).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchKFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

theorem AutomorphicForm.exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty
    (F : Type) [Field F] [NumberField F] (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ maximalCompactAt F ∅) (w : InfinitePlace F) :
    ∃ k₁ k₂ : AdelicGL2 (𝓞 F) F,
      k = k₁ * k₂ ∧ k₁ * k₂ = k₂ * k₁ ∧
      glFin (𝓞 F) F k₁ = 1 ∧
      (∀ w' : InfinitePlace F, w' ≠ w → archComponent F w' (glArch (𝓞 F) F k₁) = 1) ∧
      archComponent F w (glArch (𝓞 F) F k₁) = archComponent F w (glArch (𝓞 F) F k) ∧
      (∀ w' : InfinitePlace F, IsRowIsometry (archComponent F w' (glArch (𝓞 F) F k₁))) ∧
      k₂ ∈ maximalCompactAt F ∅ ∧ archComponent F w (glArch (𝓞 F) F k₂) = 1 := by
  revert F k _hk w
  exact @_root_.P2MW.S_AutomorphicForm_exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty.solution
