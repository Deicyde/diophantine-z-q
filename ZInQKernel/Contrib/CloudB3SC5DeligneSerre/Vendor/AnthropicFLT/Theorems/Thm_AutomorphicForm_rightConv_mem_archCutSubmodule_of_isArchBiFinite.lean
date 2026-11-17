/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite (git blob 31358c78390d9b8c11783bb1a4bbbec7b8494e54, sha256 87debf5bcd17d9b872d3836abaf9ae0f0e7eb7cfafab98b0093001e01b7ce631).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped ENNReal

theorem AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (g : AdelicGL2 (𝓞 F) F → ℂ) (hg : Continuous g)
    (α : AdelicGL2 (𝓞 F) F → ℂ) (hα : IsFactorizableTestFn F α) (hαt : IsArchBiFinite F tys α) :
    rightConv F g α ∈ archCutSubmodule F tys := by
  revert F tys g hg α hα hαt
  exact @_root_.P2MW.S_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite.solution
