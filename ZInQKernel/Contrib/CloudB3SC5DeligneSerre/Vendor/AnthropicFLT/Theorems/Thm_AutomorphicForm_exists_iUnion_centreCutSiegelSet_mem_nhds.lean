/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds (git blob 1ebbb314bc655228c53066b4fdce3239bb584c50, sha256 3bb7d3b3d74746c90d9a4b2188484596122f57c5134c14e9aa4cf75e6ff54a6c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped Topology

theorem AutomorphicForm.exists_iUnion_centreCutSiegelSet_mem_nhds (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    ∃ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c ∧ 0 < d₁ ∧
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∈ 𝓝 g := by
  revert F g
  exact @_root_.P2MW.S_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds.solution
