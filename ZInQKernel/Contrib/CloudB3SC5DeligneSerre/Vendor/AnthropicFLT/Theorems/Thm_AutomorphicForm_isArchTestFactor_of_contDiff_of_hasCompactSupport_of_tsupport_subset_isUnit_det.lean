/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det (git blob a8f9d776cd5effdbed3afe0c75b57f8b863f37e7, sha256 e044c815a779450fec3e96b0ae8c790ffdde289616be1dceb8c59801ce2e1120).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField
open scoped Classical in

theorem AutomorphicForm.isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det
    (F : Type) [Field F] [NumberField F] (Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    (hU : tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    IsArchTestFactor F fun g => Φ (archEntries F g) := by
  revert F Φ hΦ hc hU
  exact @_root_.P2MW.S_AutomorphicForm_isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det.solution
